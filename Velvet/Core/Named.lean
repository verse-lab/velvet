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

/-! ## Source references -/

/-- Quote the source range of `stx` as a term. -/
public meta def sourceRefTerm (stx : Syntax) : MacroM (TSyntax `term) := do
  let some range := stx.getRange? | `(none)
  let start : TSyntax `term := ⟨Syntax.mkNumLit (toString range.start.byteIdx)⟩
  let stop : TSyntax `term := ⟨Syntax.mkNumLit (toString range.stop.byteIdx)⟩
  `(some (Lean.Syntax.ofRange {
      start := String.Pos.Raw.mk $start
      stop := String.Pos.Raw.mk $stop }))

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

/-- Metadata key carrying the source reference of a VC whose `Named.mk` was removed. -/
public def sourceRefAnnotationKey : Name := `velvet.named.sourceRef

public def annotateSourceRef (type : Expr) (source : Syntax) : Expr :=
  .mdata (KVMap.empty.setSyntax sourceRefAnnotationKey source) type

public partial def sourceRef? : Expr → Option Syntax
  | .mdata data body =>
      match data.find sourceRefAnnotationKey with
      | some (.ofSyntax source) => some source
      | _ => sourceRef? body
  | _ => none

/-! ## Named values -/

/-- `value`, with a name and source location attached. -/
@[expose, grind .]
public def mk {α : Sort u} (_name : Name) (_stx : Option Syntax) (value : α) : α := value

public theorem mk_eq {α : Sort u} (name : Name) (stx : Option Syntax) (value : α) :
    mk name stx value = value := rfl

/-- A named `decreasing` measure. -/
public structure Measure where
  name : Name
  stx : Option Syntax
  value : Nat

/-- How `Named.mk` prints. -/
syntax:max "⟪" ident " : " term "⟫" : term

macro_rules
  | `(⟪ $name:ident : $value:term ⟫) => do
      let nameStr := Lean.Syntax.mkStrLit name.getId.toString
      let source ← sourceRefTerm value.raw
      `(Named.mk (Lean.Name.mkSimple $nameStr) $source $value)

syntax:max "named[" ident "] " term : term

macro_rules
  | `(named[$name:ident] $value:term) => do
      let nameStr := Lean.Syntax.mkStrLit name.getId.toString
      let source ← sourceRefTerm value.raw
      `(Named.mk (Lean.Name.mkSimple $nameStr) $source $value)

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

open Lean.Order in
@[app_unexpander CompleteLattice.ofProp]
public meta def unexpandOfProp : Lean.PrettyPrinter.Unexpander
  | `($(_) $p) => `(⌜$p⌝)
  | _ => throw ()

/-! ## Building assertions -/

/-- `named_assertion%[name, source] P` names the `Prop` at the end of the assertion `P`, under its
binders, and wraps it in `⌜·⌝`, which marks it for vcgen to introduce as its own hypothesis. `P`
is a `Prop` or a function into one, over whatever the assertion depends on (the result, the
state, an exception, …). `⟪name : Q⟫` is how `Named.mk` prints.

    named_assertion%[`res_le, src] (res ≤ n)
      -- ⌜⟪res_le : res ≤ n⟫⌝
    named_assertion%[`ensures1, src] (fun result s => result = s)
      -- fun result s => ⌜⟪ensures1 : result = s⟫⌝
    named_assertion%[`inv, src] p    -- p : Nat → Bool → Prop
      -- fun a a_1 => ⌜⟪inv : p a a_1⟫⌝ -/
syntax (name := namedAssertion) "named_assertion%[" term ", " term "] " term:max : term

private meta partial def liftNamedAssertion (name stx value type : Expr) : TermElabM Expr := do
  let type ← instantiateMVars (← whnf type)
  if type.isProp then
    let named ← mkAppM ``Named.mk #[name, stx, value]
    let inst := Lean.mkConst ``Std.Internal.Order.instCompleteLatticeProp
    return mkApp3 (Lean.mkConst ``Lean.Order.CompleteLattice.ofProp [0]) (mkSort 0) inst named
  match type with
  | .forallE binderName domain body binderInfo =>
      withLocalDecl binderName binderInfo domain fun x => do
        let lifted ← liftNamedAssertion name stx (mkApp value x).headBeta (body.instantiate1 x)
        mkLambdaFVars #[x] lifted
  | _ =>
      /- Fires when a named assertion does not end in `Prop` after following its function
         binders, e.g. `named_assertion%[n, s] (fun _ => (1 : Nat))`. -/
      throwError "named assertion must return Prop, but has type{indentExpr type}"

/-- Report an assertion whose arguments differ from those of the expected assertion type at the
assertion itself, before Lean's type mismatch would. -/
private meta def checkAssertionArgs (name : Expr) (valueStx : Syntax) (valueType expected : Expr) :
    TermElabM Unit := do
  -- It fits if Lean accepts it, possibly through a coercion, e.g. `False` as an `Option` failure
  -- condition `Unit → Prop`.
  let saved ← saveState
  let fits ← try
      discard <| ensureHasType expected (← mkFreshExprMVar valueType)
      pure true
    catch _ => pure false
  saved.restore
  if fits then return
  let label := match name.name?, name.app1? ``Name.mkSimple with
    | some name, _ => m!"`{name}`"
    | none, some (.lit (.strVal name)) => m!"`{name}`"
    | _, _ => m!"this assertion"
  forallTelescopeReducing expected fun xs _ => forallTelescopeReducing valueType fun ys _ => do
    let xTypes ← xs.mapM fun x => inferType x
    let yTypes ← ys.mapM fun y => inferType y
    if xs.size != ys.size then
      let types := MessageData.joinSep (xTypes.toList.map fun t => m!"{t}") ", "
      let args := if xs.size == 1 then "argument" else "arguments"
      let takes := if ys.isEmpty then m!"none" else m!"{ys.size}"
      /- Fires when an assertion has too few or too many arguments for the monad, e.g.
         `requires x > 0` in `StateM Nat`, which needs the state `(s : Nat) => …`. -/
      throwErrorAt valueStx "{label} must take {xs.size} {args} ({types}), but takes {takes}"
    for i in [:xs.size] do
      unless ← isDefEq xTypes[i]! yTypes[i]! do
        /- Fires when an argument of an assertion has the wrong type, e.g.
           `requires (s : Bool) => …` in `StateM Nat`. -/
        throwErrorAt valueStx
          "argument {i + 1} of {label} has type{indentExpr yTypes[i]!}\nbut should have type{indentExpr xTypes[i]!}"

@[term_elab namedAssertion]
public meta def elabNamedAssertion : TermElab := fun stx expectedType? => do
  let `(named_assertion%[$nameStx, $sourceStx] $valueStx) := stx | throwUnsupportedSyntax
  let name ← elabTerm nameStx none
  let source ← elabTerm sourceStx (some (mkApp (mkConst ``Option [0]) (mkConst ``Syntax)))
  let value ← elabTerm valueStx expectedType?
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  let valueType ← instantiateMVars (← inferType value)
  -- Only an assertion with a known expected type is checked, e.g. a method's clause, which the
  -- method ascribes with `assertion_type%`.
  if let some expected := expectedType? then
    let expected ← instantiateMVars expected
    unless expected.hasExprMVar do
      checkAssertionArgs name valueStx valueType expected
  liftNamedAssertion name source value valueType

/-- `assertion_meet%[P, Q]` is the meet of the assertions `P` and `Q`, which have the same type:
it puts `⊓` between the `Prop`s at their ends, under their shared binders. Like
`named_assertion%`, it takes a `Prop` or a function into one. Several named assertions are
combined as a right-nested chain of these.

    assertion_meet%[(res ≤ n), (0 < n)]
      -- (res ≤ n) ⊓ (0 < n)
    assertion_meet%[(fun result s => result = s), (fun result s => s ≤ 10)]
      -- fun result s => (result = s) ⊓ (s ≤ 10)
    assertion_meet%[named_assertion%[`a, src] (res ≤ n),
      assertion_meet%[named_assertion%[`b, src] (0 < n), named_assertion%[`c, src] (n < 10)]]
      -- ⌜⟪a : res ≤ n⟫⌝ ⊓ (⌜⟪b : 0 < n⟫⌝ ⊓ ⌜⟪c : n < 10⟫⌝) -/
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
      /- Fires when meeting assertions that do not end in `Prop`, e.g.
         `assertion_meet%[(fun _ => (1 : Nat)), (fun _ => True)]`. -/
      throwError "assertion meet must return Prop, but has type{indentExpr type}"

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

/-- The names of a list of clauses: the given name, or `pref` followed by the clause's position,
e.g. `requires1`, `invariant2`. -/
public def clauseNames (ids : Array (Option Ident)) (pref : String) : Array Name :=
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
      `(named_assertion%[$nameTerm, $stxTerm] $(ts[i]!))
    let lastIdx := ts.size - 1
    let mut result ← named lastIdx
    for i in List.range lastIdx |>.reverse do
      result ← `(assertion_meet%[$(← named i), $result])
    return result

/-- `signals%[e₁, …, eₙ]` builds the exception postcondition the expected type asks for, one
clause per exception: a single assertion, a pair, or an exception stack `EStack⟨…⟩`.

    signals%[fun e => e = "bad"]                         -- String → Prop
      -- fun e => e = "bad"
    signals%[fun e s => e = "bad" ∧ s = 42, fun _ => False]  -- (String → Nat → Prop) × (Unit → Prop)
      -- (fun e s => e = "bad" ∧ s = 42, fun x => False)
    signals%[fun e => e = "bad", fun n => n = 0]         -- EStack⟨String → Prop, Nat → Prop⟩
      -- estack⟨fun e => e = "bad", fun n => n = 0⟩
    signals%[]                                           -- EStack⟨⟩
      -- estack⟨⟩

With named assertions:

    signals%[named_assertion%[`signals1, src] (fun e s => e = "bad" ∧ s = 42),
      named_assertion%[`signals2, src] False]            -- (String → Nat → Prop) × (Unit → Prop)
      -- (fun e s => ⌜⟪signals1 : e = "bad" ∧ s = 42⟫⌝, fun x => ⌜⟪signals2 : False⟫⌝)
    signals%[named_assertion%[`bad, src] (fun e => e = "bad"),
      named_assertion%[`zero, src] (fun n => n = 0)]     -- EStack⟨String → Prop, Nat → Prop⟩
      -- estack⟨fun e => ⌜⟪bad : e = "bad"⟫⌝, fun n => ⌜⟪zero : n = 0⟫⌝⟩ -/
syntax (name := signalsList) "signals%[" term,* "]" : term

@[term_elab signalsList]
public meta def elabSignalsList : TermElab := fun stx expectedType? => do
  let `(signals%[$terms,*]) := stx | throwUnsupportedSyntax
  let expectedType ← tryPostponeIfHasMVars expectedType?
    "signals require an expected assertion type"
  -- Errors point at the user's clause, not at its generated `named_assertion%` wrapper.
  let clause (t : Syntax) : Syntax :=
    if t.isOfKind ``namedAssertion then t[t.getNumArgs - 1] else t
  let lastRef := (terms.getElems.back?.map (clause ·.raw)).getD stx
  let rec build (type : Expr) (remaining : List (TSyntax `term)) : TermElabM Expr := do
    let type ← whnf type
    -- An exception postcondition stack `EStack⟨e₁, …, eₙ⟩` is `e₁ × … × eₙ × EStackEnd`, and
    -- `EStackEnd` reduces to `Unit`.
    if type.isConstOf ``PUnit then
      if let extra :: _ := remaining then
        throwErrorAt (clause extra) "too many `signals` clauses"
      return mkConst ``Std.WP.EStackEnd.mk
    if let some (headType, tailType) := type.app2? ``Prod then
      let head :: tail := remaining
        | throwErrorAt lastRef "missing a `signals` clause for{indentExpr headType}"
      return ← mkAppM ``Prod.mk
        #[← elabTermEnsuringType head headType, ← build tailType tail]
    match remaining with
    | [term] => elabTermEnsuringType term type
    | [] => throwErrorAt lastRef "missing a `signals` clause for{indentExpr type}"
    | _ :: extra :: _ => throwErrorAt (clause extra) "too many `signals` clauses"
  build expectedType terms.getElems.toList

public meta def mkSignalsList (ts : Array (TSyntax `term)) (names : Array Name) : MacroM (TSyntax `term) := do
  let terms ← ts.mapIdxM fun i term => do
    let nameStr := Lean.Syntax.mkStrLit names[i]!.toString
    let nameTerm ← `(Lean.Name.mkSimple $nameStr)
    let stxTerm ← sourceRefTerm term.raw
    `(named_assertion%[$nameTerm, $stxTerm] $term)
  `(signals%[$terms,*])

/-! ## Reading named assertions -/

public structure Info where
  name : Name
  source? : Option Syntax
  value : Expr

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

public def extract? (type : Expr) : SymM (Option (Name × Expr)) := do
  return (← extractInfo? type).map fun info => (info.name, info.value)

end Named
