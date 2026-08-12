module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.Tactic.Cases
public import Lean.Meta.Tactic.Rename
public import Lean.Meta.Tactic.Replace
public import Lean.Meta.Sym.SymM

open Lean Meta Elab Lean.Meta.Sym

namespace Named

/--
Attach a user-facing name and source syntax to a value without changing its
denotation. Verification tooling can inspect the wrapper before unfolding it.
-/
@[expose, grind .]
public def mk {α : Sort u} (_name : Name) (_stx : Option Syntax) (value : α) : α :=
  value

/-- Local proof rule for explicitly removing a `Named.mk` wrapper without making it a global simp
normalization rule. -/
public theorem mk_eq {α : Sort u} (name : Name) (stx : Option Syntax) (value : α) :
    mk name stx value = value := rfl

/-- A named natural-number measure used to formulate decreasing obligations. -/
public structure Measure where
  name : Name
  stx : Option Syntax
  value : Nat

/-- Compact output syntax used by the `Named.mk` unexpander. -/
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

/-- Pretty-print `Named.mk` applications as `⟪name : value⟫`. -/
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

/-- Extract the outer `Named.mk` annotation, following an application spine. -/
public partial def extract? (type : Expr) : SymM (Option (Name × Expr)) := do
  -- We expect already instantiated..
  /- let type ← instantiateMVars type -/
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
  if type.isAppOf ``Named.mk then
    true
  else if type.isAppOfArity ``And 2 then
    contains (type.getArg! 0) || contains (type.getArg! 1)
  else
    match type with
    | .app fn _ => contains fn
    | _ => false

/--
Unwrap and name every `Named.mk ... p` proposition in a goal's hypotheses.
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
Unwrap a `Named.mk ... p` target, changing it to `p` and setting the goal's case
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

end Named
