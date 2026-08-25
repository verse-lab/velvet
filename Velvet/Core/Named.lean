module

prelude
public import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Elab.SyntheticMVars
public import Lean.Meta.Tactic.Cases
public import Lean.Meta.Tactic.Rename
public import Lean.Meta.Tactic.Replace
public meta import Lean.Meta.Sym.SymM
public import Std.WP

open Lean Meta Elab Term Lean.Meta.Sym

namespace Named

attribute [instance] Std.Internal.Order.instCompleteLatticeProp
attribute [instance] Std.Internal.Order.instPartialOrderProp

/-- Attach a user-facing name and source syntax without changing a value's denotation. -/
@[expose, grind .]
public def mk {α : Sort u} (_name : Name) (_stx : Option Syntax) (value : α) : α := value

/-- Quote only the source range of `stx`. The resulting syntax object is suitable as an error
reference without retaining or reconstructing the full annotation syntax tree. -/
public meta def sourceRefTerm (stx : Syntax) : MacroM (TSyntax `term) := do
  let some range := stx.getRange? | `(none)
  let start : TSyntax `term := ⟨Syntax.mkNumLit (toString range.start.byteIdx)⟩
  let stop : TSyntax `term := ⟨Syntax.mkNumLit (toString range.stop.byteIdx)⟩
  `(some (Lean.Syntax.ofRange {
      start := String.Pos.Raw.mk $start
      stop := String.Pos.Raw.mk $stop }))

public theorem mk_eq {α : Sort u} (name : Name) (stx : Option Syntax) (value : α) :
    mk name stx value = value := rfl

open Lean.Order in
/-- Pretty-print proposition embeddings using the standard `⌜P⌝` assertion notation. -/
@[app_unexpander CompleteLattice.ofProp]
public meta def unexpandOfProp : Lean.PrettyPrinter.Unexpander
  | `($(_) $p) => `(⌜$p⌝)
  | _ => throw ()

/-- Internal syntax used by loop-annotation generation. It inserts `CompleteLattice.ofProp` at the
`Prop` leaf of an assertion, recursively underneath function binders. -/
syntax (name := namedClause) "named_clause%[" term ", " term "] " term:max : term

private meta partial def liftNamedClause (name stx value type : Expr) : TermElabM Expr := do
  let type ← instantiateMVars (← whnf type)
  if type.isProp then
    let named ← mkAppM ``Named.mk #[name, stx, value]
    let inst := Lean.mkConst ``Std.Internal.Order.instCompleteLatticeProp
    return mkApp3 (Lean.mkConst ``Lean.Order.CompleteLattice.ofProp [0]) (mkSort 0) inst named
  match type with
  | .forallE binderName domain body binderInfo =>
      withLocalDecl binderName binderInfo domain fun x => do
        let lifted ← liftNamedClause name stx (mkApp value x) (body.instantiate1 x)
        mkLambdaFVars #[x] lifted
  | _ =>
      /- Fires when a named loop assertion does not end in `Prop` after following its function
         binders, e.g. `named_clause%[n, s] (fun _ => (1 : Nat))`. -/
      throwError "named loop assertion must return Prop, but has type{indentExpr type}"

@[term_elab namedClause]
public meta def elabNamedClause : TermElab := fun stx expectedType? => do
  let `(named_clause%[$nameStx, $sourceStx] $valueStx) := stx | throwUnsupportedSyntax
  let name ← elabTerm nameStx none
  let source ← elabTerm sourceStx none
  let value ← elabTerm valueStx expectedType?
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  let valueType ← instantiateMVars (← inferType value)
  liftNamedClause name source value valueType

/-- Internal pointwise meet used by loop-annotation generation. -/
syntax (name := assertionMeet) "assertion_meet%[" term ", " term "]" : term

private meta partial def meetAssertions (lhs rhs type : Expr) : TermElabM Expr := do
  let type ← instantiateMVars (← whnf type)
  if type.isProp then
    let inst := Lean.mkConst ``Std.Internal.Order.instCompleteLatticeProp
    return mkApp4 (Lean.mkConst ``Lean.Order.meet [0]) (mkSort 0) inst lhs rhs
  match type with
  | .forallE binderName domain body binderInfo =>
      withLocalDecl binderName binderInfo domain fun x => do
        let lhs := (mkApp lhs x).headBeta
        let rhs := (mkApp rhs x).headBeta
        let meet ← meetAssertions lhs rhs (body.instantiate1 x)
        mkLambdaFVars #[x] meet
  | _ =>
      /- Fires when pointwise-meeting loop assertions that are not `Prop`-valued, e.g.
         `assertion_meet%[(fun _ => (1 : Nat)), (fun _ => True)]`. -/
      throwError "loop assertion meet must return Prop, but has type{indentExpr type}"

@[term_elab assertionMeet]
public meta def elabAssertionMeet : TermElab := fun stx expectedType? => do
  let `(assertion_meet%[$lhsStx, $rhsStx]) := stx | throwUnsupportedSyntax
  let lhs ← elabTerm lhsStx expectedType?
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let lhs ← instantiateMVars lhs
  let lhsType ← instantiateMVars (← inferType lhs)
  let rhs ← elabTermEnsuringType rhsStx lhsType
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let rhs ← instantiateMVars rhs
  meetAssertions lhs rhs lhsType

/-- A named natural-number measure used to formulate decreasing obligations. -/
public structure Measure where
  name : Name
  stx : Option Syntax
  value : Nat

/-- Compact output syntax used by the named-assertion unexpander. -/
syntax:max "⟪" ident " : " term "⟫" : term

macro_rules
  | `(⟪ $name:ident : $value:term ⟫) => do
      let nameStr := Lean.Syntax.mkStrLit name.getId.toString
      let source ← sourceRefTerm value.raw
      `(Named.mk (Lean.Name.mkSimple $nameStr) $source $value)

/-- Attach a name and captured source syntax to a value. -/
syntax:max "named[" ident "] " term : term

macro_rules
  | `(named[$name:ident] $value:term) => do
      let nameStr := Lean.Syntax.mkStrLit name.getId.toString
      let source ← sourceRefTerm value.raw
      `(Named.mk (Lean.Name.mkSimple $nameStr) $source $value)

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

/-- Expression-metadata key used to carry an annotation's source reference after `Named.mk`
has been removed from an emitted VC target. -/
public def sourceRefAnnotationKey : Name := `velvet.named.sourceRef

public def annotateSourceRef (type : Expr) (source : Syntax) : Expr :=
  .mdata (KVMap.empty.setSyntax sourceRefAnnotationKey source) type

public partial def sourceRef? : Expr → Option Syntax
  | .mdata data body =>
      match data.find sourceRefAnnotationKey with
      | some (.ofSyntax source) => some source
      | _ => sourceRef? body
  | _ => none

/-- Metadata extracted from an application of `Named.mk`. -/
public structure Info where
  name : Name
  source? : Option Syntax
  value : Expr

private def decodeRawPos? (e : Expr) : MetaM (Option String.Pos.Raw) := do
  let e ← whnf e
  let_expr String.Pos.Raw.mk n := e | return none
  return (← getNatValue? n).map String.Pos.Raw.mk

private def decodeSourceRef? (e : Expr) : MetaM (Option Syntax) := do
  let e ← whnf e
  match_expr e with
  | Option.none _α => return none
  | Option.some _α source =>
      let_expr Syntax.ofRange range canonical := source | return none
      unless canonical.isConstOf ``Bool.true do return none
      let_expr Syntax.Range.mk start stop := range | return none
      let some start ← decodeRawPos? start | return none
      let some stop ← decodeRawPos? stop | return none
      return some (Syntax.ofRange { start, stop })
  | _ => return none

/-- Extract a named proposition atom and its source reference, following an application spine. -/
public partial def extractInfo? (type : Expr) : SymM (Option Info) := do
  let type := type.headBeta.consumeMData
  if type.isAppOf ``Lean.Order.CompleteLattice.ofProp then
    return ← extractInfo? type.appArg!
  match_expr type with
  | Named.mk _α name source value =>
      /- Fires when a `Named.mk` wraps a non-literal name, e.g. one built by a computed `Name`
         rather than `Lean.Name.mkSimple "..."`. -/
      let some name := name.name?
        | throwError "invalid Named.mk name: {name}"
      return some { name, source? := ← decodeSourceRef? source, value }
  | _ =>
      match type with
      | .mdata _ body => extractInfo? body
      | .forallE _ _ body _ => extractInfo? body
      | .letE _ _ _ body _ => extractInfo? body
      | .app fn arg =>
          let some info ← extractInfo? fn | return none
          return some { info with value := (Expr.app info.value arg).headBeta }
      | _ => return none

/-- Extract a named proposition atom, following an application spine. -/
public def extract? (type : Expr) : SymM (Option (Name × Expr)) := do
  return (← extractInfo? type).map fun info => (info.name, info.value)

/-- Fill in `requires`/`ensures`/`signals`/`invariant` names that were not given explicitly. -/
public def makeNameArrayFromIdents (ids : Array (Option Ident)) (pref : String) : Array Name :=
  ids.mapIdx fun i e =>
    match e with
    | some id => id.getId
    | none => Name.mkSimple s!"{pref}{i+1}"

public meta def mkAssertionList (ts : Array (TSyntax `term)) (names : Array Name) : MacroM (TSyntax `term) := do
  if ts.isEmpty then
    `(term| (True : Prop))
  else
    let named (i : Nat) : MacroM (TSyntax `term) := do
      let name := names[i]!.toString
      let nameStr := Lean.Syntax.mkStrLit name
      let nameTerm ← `(Lean.Name.mkSimple $nameStr)
      let stxTerm ← sourceRefTerm ts[i]!.raw
      `(named_clause%[$nameTerm, $stxTerm] $(ts[i]!))
    let lastIdx := ts.size - 1
    let mut result ← named lastIdx
    for i in List.range lastIdx |>.reverse do
      result ← `(assertion_meet%[$(← named i), $result])
    return result



public meta def mkSignalsList (ts : Array (TSyntax `term)) (names : Array Name) : MacroM (TSyntax `term) := do
  if ts.isEmpty then
    `(term| ⟨⟩)
  else
    let named (i : Nat) : MacroM (TSyntax `term) := do
      let name := names[i]!.toString
      let nameStr := Lean.Syntax.mkStrLit name
      let nameTerm ← `(Lean.Name.mkSimple $nameStr)
      let stxTerm ← sourceRefTerm ts[i]!.raw
      `(named_clause%[$nameTerm, $stxTerm] $(ts[i]!))
    if ts.size == 1 then
      named 0
    else
      let lastIdx := ts.size - 1
      let mut result ← named lastIdx
      for i in List.range lastIdx |>.reverse do
        result ← `(($(← named i), $result))
      return result

end Named
