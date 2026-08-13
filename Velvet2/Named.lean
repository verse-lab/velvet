module

prelude
public import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Term.TermElabM
public import Lean.Meta.Tactic.Cases
public import Lean.Meta.Tactic.Rename
public import Lean.Meta.Tactic.Replace
public meta import Lean.Meta.Sym.SymM
public import Std.Internal.Do.Order.Basic

open Lean Meta Elab Term Lean.Meta.Sym

namespace Named

/-- Attach a user-facing name and source syntax without changing a value's denotation. -/
@[expose, grind .]
public def mk {α : Sort u} (_name : Name) (_stx : Option Syntax) (value : α) : α := value

public theorem mk_eq {α : Sort u} (name : Name) (stx : Option Syntax) (value : α) :
    mk name stx value = value := rfl

/-- Internal syntax used by loop-annotation generation. It inserts `CompleteLattice.ofProp` at the
`Prop` leaf of an assertion, recursively underneath function binders. -/
syntax (name := namedLoopClause) "named_loop_clause%[" term ", " term "] " term:max : term

private meta partial def liftLoopClause (name stx value type : Expr) : TermElabM Expr := do
  let type ← whnf type
  if type.isProp then
    let named ← mkAppM ``Named.mk #[name, stx, value]
    let inst := Lean.mkConst ``Lean.Order.instCompleteLatticeProp_std
    return mkApp3 (Lean.mkConst ``Lean.Order.CompleteLattice.ofProp [0]) (mkSort 0) inst named
  match type with
  | .forallE binderName domain body binderInfo =>
      withLocalDecl binderName binderInfo domain fun x => do
        let lifted ← liftLoopClause name stx (mkApp value x) (body.instantiate1 x)
        mkLambdaFVars #[x] lifted
  | _ =>
      throwError "named loop assertion must return Prop, but has type{indentExpr type}"

@[term_elab namedLoopClause]
public meta def elabNamedLoopClause : TermElab := fun stx expectedType? => do
  let `(named_loop_clause%[$nameStx, $sourceStx] $valueStx) := stx | throwUnsupportedSyntax
  let name ← elabTerm nameStx none
  let source ← elabTerm sourceStx none
  let value ← elabTerm valueStx expectedType?
  liftLoopClause name source value (← inferType value)

/-- Internal pointwise meet used by loop-annotation generation. -/
syntax (name := assertionMeet) "assertion_meet%[" term ", " term "]" : term

private meta partial def meetAssertions (lhs rhs type : Expr) : TermElabM Expr := do
  let type ← whnf type
  if type.isProp then
    let inst := Lean.mkConst ``Lean.Order.instCompleteLatticeProp_std
    return mkApp4 (Lean.mkConst ``Lean.Order.meet [0]) (mkSort 0) inst lhs rhs
  match type with
  | .forallE binderName domain body binderInfo =>
      withLocalDecl binderName binderInfo domain fun x => do
        let lhs := (mkApp lhs x).headBeta
        let rhs := (mkApp rhs x).headBeta
        let meet ← meetAssertions lhs rhs (body.instantiate1 x)
        mkLambdaFVars #[x] meet
  | _ =>
      throwError "loop assertion meet must return Prop, but has type{indentExpr type}"

@[term_elab assertionMeet]
public meta def elabAssertionMeet : TermElab := fun stx expectedType? => do
  let `(assertion_meet%[$lhsStx, $rhsStx]) := stx | throwUnsupportedSyntax
  let lhs ← elabTerm lhsStx expectedType?
  let lhsType ← inferType lhs
  let rhs ← elabTermEnsuringType rhsStx lhsType
  meetAssertions lhs rhs lhsType

/-- A named natural-number measure used to formulate decreasing obligations. -/
public structure Measure where
  name : Name
  stx : Option Syntax
  value : Nat

/-- Compact output syntax used by the named-assertion unexpander. -/
syntax:max "⟪" ident " : " term "⟫" : term

/-- Attach a name and captured source syntax to a value. -/
syntax:max "named[" ident "] " term : term

macro_rules
  | `(named[$name:ident] $value:term) => do
      let nameStr := Lean.Syntax.mkStrLit name.getId.toString
      let text := value.raw.reprint.getD (toString value.raw.formatStx)
      let textStr := Lean.Syntax.mkStrLit text
      `(Named.mk
        (Lean.Name.mkSimple $nameStr)
        (some (Lean.Syntax.atom Lean.SourceInfo.none $textStr))
        $value)

/-- Pretty-print named proposition atoms as `⟪name : value⟫`. -/
@[app_unexpander Named.mk, app_unexpander Named.Measure.mk]
public meta def unexpandMk : Lean.PrettyPrinter.Unexpander
  | `($(_) $name $_stx $value) => do
      let ident ← match name with
        | `(Lean.Name.mkSimple $name:str) =>
            pure <| mkIdent (Name.mkSimple name.getString)
        | _ =>
            if name.raw.isOfKind ``Lean.Parser.Term.quotedName then
              if let some name := name.raw[0].isNameLit? then
                pure <| mkIdent name
              else
                throw ()
            else
              throw ()
      `(⟪ $ident : $value ⟫)
  | _ => throw ()

/-- Extract a named proposition atom, following an application spine. -/
public partial def extract? (type : Expr) : SymM (Option (Name × Expr)) := do
  match_expr type with
  | Named.mk _α name _stx value =>
      let some name := name.name?
        | throwError "invalid Named.mk name: {name}"
      return some (name, value)
  | _ =>
      match type with
      | .mdata _ body =>
          extract? body
      | .app fn arg =>
          let some (name, value) ← extract? fn
            | return none
          return some (name, (Expr.app value arg).headBeta)
      | _ => return none

/-- Whether an expression is a named value or an `And` tree containing one. -/
public partial def contains (type : Expr) : Bool :=
  if type.getAppFn.isConstOf ``Named.mk then
    true
  else if type.isAppOfArity ``And 2 then
    contains (type.getArg! 0) || contains (type.getArg! 1)
  else
    match type with
    | .app fn _ => contains fn
    | _ => false

/--
Unwrap and name every named proposition in a goal's hypotheses.
Structural conjunctions are split only when they contain named propositions.
-/
public partial def processHyp (goal : MVarId) : SymM (List MVarId) :=
  goal.withContext do
    for localDecl in ← getLCtx do
      if localDecl.isImplementationDetail then
        continue
      let type ← instantiateMVars localDecl.type
      if let some type ← withReducible <| reduceRecMatcher? type then
        let goal ← goal.replaceLocalDeclDefEq localDecl.fvarId type
        return ← processHyp goal
      if let some (name, prop) ← extract? type then
        let goal ← goal.rename localDecl.fvarId name
        let goal ← goal.replaceLocalDeclDefEq localDecl.fvarId prop
        return ← processHyp goal
      let type ← whnfR type
      if type.isAppOfArity ``And 2 && contains (type.getArg! 0) && contains (type.getArg! 1) then
        let subgoals ← goal.cases localDecl.fvarId
        let mut results := []
        for subgoal in subgoals do
          results := results ++ (← processHyp subgoal.mvarId)
        return results
    return [goal]

/--
Unwrap a named target, changing it to its proposition and setting the goal's case
tag to the encoded name.
-/
public def processGoal (goal : MVarId) : SymM (List MVarId) :=
  goal.withContext do
    let target ← goal.getType
    if let some (name, prop) ← extract? target then
      let goal ← goal.replaceTargetDefEq prop
      goal.setTag name
      return [goal]
    return [goal]

/-- Build an `And` tree whose leaves are individually named propositions. -/
public def mkPropList (ts : Array (TSyntax `term)) (names : Array (Option Name) := #[])
    (pfx : String := "clause") : MacroM (TSyntax `term) := do
  if ts.isEmpty then
    `(term| True)
  else
    let namedMk := mkIdent ``Named.mk
    let getName (i : Nat) : MacroM (TSyntax `term) := do
      let name := match names[i]? with
        | some (some name) => name.toString
        | _ => s!"{pfx}{i + 1}"
      let nameStr := Lean.Syntax.mkStrLit name
      `(Lean.Name.mkSimple $nameStr)
    let getStx (i : Nat) : MacroM (TSyntax `term) := do
      let text := ts[i]!.raw.reprint.getD (toString (ts[i]!.raw.formatStx))
      let textStr := Lean.Syntax.mkStrLit text
      `(some (Lean.Syntax.atom Lean.SourceInfo.none $textStr))
    let named (i : Nat) : MacroM (TSyntax `term) := do
      let name ← getName i
      let stx ← getStx i
      `($namedMk ($name) ($stx) $(ts[i]!))
    let lastIdx := ts.size - 1
    let mut result ← named lastIdx
    for i in List.range lastIdx |>.reverse do
      result ← `($(← named i) ∧ $result)
    return result

/-- Build a lattice meet tree whose leaves are individually named assertions. Unlike `mkPropList`,
this supports function-valued assertion languages such as StateT and ReaderT predicates. -/
public def mkAssertionList (ts : Array (TSyntax `term)) (names : Array (Option Name) := #[])
    (pfx : String := "clause") : MacroM (TSyntax `term) := do
  if ts.isEmpty then
    let top := mkIdent ``Lean.Order.top
    `(term| $top)
  else
    let named (i : Nat) : MacroM (TSyntax `term) := do
      let name := match names[i]? with
        | some (some name) => name.toString
        | _ => s!"{pfx}{i + 1}"
      let nameStr := Lean.Syntax.mkStrLit name
      let nameTerm ← `(Lean.Name.mkSimple $nameStr)
      let text := ts[i]!.raw.reprint.getD (toString (ts[i]!.raw.formatStx))
      let textStr := Lean.Syntax.mkStrLit text
      let stxTerm ← `(some (Lean.Syntax.atom Lean.SourceInfo.none $textStr))
      `(named_loop_clause%[$nameTerm, $stxTerm] $(ts[i]!))
    let lastIdx := ts.size - 1
    let mut result ← named lastIdx
    for i in List.range lastIdx |>.reverse do
      result ← `(assertion_meet%[$(← named i), $result])
    return result

end Named
