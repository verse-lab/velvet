module

public import Velvet.Frontend.Types
public meta import Velvet.Frontend.Types
public import Velvet.Core.Named
public meta import Velvet.Core.Named
public import Velvet.Core.DecidableWP
public import Velvet.Core.DecidableHeuristics
public meta import Velvet.Core.DecidableHeuristics
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic

/-!
# Contract testers

`#derive_tester_for M` builds `M.check`, which tests `M` against its contract
`Triple (M args) pre post signals` at one input by running it.

## Example

Take a program

    checked (bad : Bool) : ExceptT String (StateT Nat Option) Nat := do
      set 42
      if bad then throw "bad"
      return 42

with precondition `s < 100`, postcondition `result = s`, and the signals `e = "bad" ∧ s = 42` for
`throw e` and `False` for `Option` failing. Its WP instance gives the assertion types

    Pred  = Nat → Prop                             -- over the state
    EPred = (String → Nat → Prop) × (Unit → Prop)  -- `throw e` with the state; `Option` failing

## Deciding the clauses

`checked.preDecidable`, `checked.postDecidable` and `checked.signalsDecidable` decide each clause
at any values of its inputs, following the shape of its type (`PointwiseDecidable`):

    checked.preDecidable : Bool → (s : Nat) → Decidable ⌜⟪requires1 : s < 100⟫⌝
    checked.postDecidable : Bool → (result s : Nat) → Decidable ⌜⟪ensures1 : result = s⟫⌝
    checked.signalsDecidable : Bool →
      ((e : String) → (s : Nat) → Decidable ⌜⟪signals1 : e = "bad" ∧ s = 42⟫⌝) ×
        (Unit → Decidable ⌜⟪signals2 : False⟫⌝)

`prove_*_decidable_for M` derives one by instance search on the clause, or takes a proof;
`#derive_tester_for` derives the ones not given.

## Deciding the WP

`decideWP` (from `DecidableWP`) combines the decisions of `post` and `signals` into a decision
of `wp (checked bad) post signals`. Each layer of the monad has an instance, and here `ExceptT`,
then `StateT`, then `Option` unfold it to

    fun s => match (checked bad).run.run s with
      | some (.ok a, s')    => checked.postDecidable bad a s'
      | some (.error e, s') => (checked.signalsDecidable bad).1 e s'
      | none                => (checked.signalsDecidable bad).2 ()

so it runs `checked bad` from `s` and decides the clause for how it ended.

## The tester

`checked.check` takes the method's arguments, then the inputs of `Pred` (here the state `s`):

    def checked.check : Bool → Nat → TestVerdict :=
    fun bad s =>
      check ⌜⟪requires1 : s < 100⟫⌝ (checked.preDecidable bad s) fun unit =>
        decide
          (Std.WP.wp (checked bad) (fun result s => ⌜⟪ensures1 : result = s⟫⌝)
            (fun e s => ⌜⟪signals1 : e = "bad" ∧ s = 42⟫⌝, fun x => ⌜⟪signals2 : False⟫⌝) s)

The `Decidable` passed to `decide` is not printed: it is `decideWP (checked bad) post signals
(checked.postDecidable bad) (checked.signalsDecidable bad) s`. `check` decides the precondition:
if it does not hold, the verdict is `.discard` and `checked` never runs. Otherwise `decide` reads
the `Bool` out of the `Decidable` that `decideWP` builds: `.pass` or `.fail`. For example,
`checked.check true 0` runs `checked true` from `0`, which throws `"bad"` in state `42`, and
decides `signals1` at `"bad"` and `42`.
-/

open Lean Meta Elab Command Term
open Velvet.Testing

namespace Velvet.Testing

private meta def withContract (name : Ident)
    (k : Array Expr → Expr → Expr → Expr → Expr → Expr → TermElabM Expr) :
    TermElabM Expr := do
  let methodName ← realizeGlobalConstNoOverload name
  let specName := methodName ++ `spec_triple
  unless (methodSpecExt.getState (← getEnv)).contains methodName do
    throwErrorAt name "no method contract metadata found for `{methodName}`"
  let spec ← mkConstWithFreshMVarLevels specName
  forallTelescopeReducing spec fun args body => do
    let body ← whnf body
    let_expr Std.WP.Triple _ _ _ _ _ _ program wpInst pre post signals := body
      | throwError "expected a method Triple, got {body}"
    k args program wpInst pre post signals

/-- The `i`-th component of the pair `p`, taken directly when `p` is a pair literal. -/
private meta def pairComponent (p : Expr) (i : Nat) : Expr :=
  if p.isAppOfArity ``Prod.mk 4 then p.getArg! (i + 2) else mkProj ``Prod i p

/-- Expand only the decision structure, preserving the propositions and their binder names. -/
private meta partial def decisionType (p : Expr) : TermElabM Expr := do
  let type ← whnf (← inferType p)
  if type.isProp then
    return ← mkAppM ``Decidable #[p]
  match type with
  | .forallE name domain _ bi =>
    withLocalDecl name bi domain fun arg => do
      mkForallFVars #[arg] (← decisionType (mkApp p arg).headBeta)
  | _ =>
    -- Exception postcondition stacks `EStack⟨…⟩` are products ending in `EStackEnd`.
    if type.isAppOf ``Prod then
      return ← mkAppM ``Prod #[← decisionType (pairComponent p 0),
        ← decisionType (pairComponent p 1)]
    -- `EStackEnd` reduces to `Unit`, i.e. `PUnit`.
    if type.isConstOf ``PUnit then return mkConst ``Unit
    throwError "unsupported assertion type for pointwise decisions: {type}"

syntax (name := testingDecisionType) "testing_decision_type% " ident ident : term

@[term_elab testingDecisionType]
public meta def elabDecisionType : TermElab := fun stx _ => do
  let `(testing_decision_type% $name:ident $kind:ident) := stx | throwUnsupportedSyntax
  withContract name fun args _ _ pre post signals => do
    let p ← match kind.getId with
      | `pre => pure pre
      | `post => pure post
      | `signals => pure signals
      | _ => throwError "unknown decision kind"
    mkForallFVars args (← decisionType p)

private meta def decisionName (name : Ident) (suffix : Name) : TermElabM Name := do
  let resolved ← realizeGlobalConstNoOverload name
  return resolved ++ suffix

syntax (name := testingChecker) "testing_checker% " ident : term

@[term_elab testingChecker]
public meta def elabChecker : TermElab := fun stx _ => do
  let `(testing_checker% $name:ident) := stx | throwUnsupportedSyntax
  withContract name fun args program wpInst pre post signals => do
    let getDecision (suffix : Name) := do
      let c ← mkConstWithFreshMVarLevels (← decisionName name suffix)
      return mkAppN c args
    let preDec ← getDecision `preDecidable
    let postDec ← getDecision `postDecidable
    let signalsDec ← getDecision `signalsDecidable
    let wpDec ← mkAppM ``decideWP #[program, post, signals, postDec, signalsDec]
    let contractWP ← mkAppOptM ``Std.WP.WP.wp #[none, none, none, none, none, none,
      some wpInst, some program, some post, some signals]
    let expected ← mkAppM ``PointwiseDecidable #[contractWP]
    -- `decideWP` decides the WP of the instance that instance search finds; check that it is
    -- the one the contract is stated with.
    unless ← isDefEq (← inferType wpDec) expected do
      throwErrorAt name "DecidableWP does not match this method's WP interpretation"
    -- The inputs of `Pred` become arguments of `M.check` (see the module docstring).
    forallTelescopeReducing (← inferType pre) fun context leaf => do
      unless leaf.isProp do throwError "tester assertions must end in Prop"
      let pre := (mkAppN pre context).headBeta
      let preDec := mkAppN preDec context
      let wpDec := mkAppN wpDec context
      let decType ← whnf (← inferType wpDec)
      let_expr Decidable resultProp := decType
        | throwError "WP decision did not reduce to Decidable: {decType}"
      let result ← mkAppOptM ``decide #[some resultProp, some wpDec]
      let run ← withLocalDeclD `unit (mkConst ``Unit) fun unit => mkLambdaFVars #[unit] result
      let check ← mkAppM ``Velvet.Testing.check #[pre, preDec, run]
      mkLambdaFVars (args ++ context) check

open Lean.Elab.Tactic

/-- Introduce pointwise arguments and split exception stacks without choosing a truth value. -/
private meta partial def prepareDecisions (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    let type ← whnf (← goal.getType)
    if type.isForall then
      let (_, next) ← goal.intro1P
      return ← prepareDecisions next
    if type.isAppOf ``Prod then
      let goals ← goal.apply (← mkConstWithFreshMVarLevels ``Prod.mk)
      return (← goals.mapM prepareDecisions).flatten
    if ← isDefEq type (mkConst ``Unit) then
      goal.assign (mkConst ``Unit.unit)
      return []
    return [goal]

elab "prepare_testing_decisions" : tactic => do
  setGoals ((← (← getGoals).mapM prepareDecisions).flatten)

syntax "prove_precondition_decidable_for " ident (" by " tacticSeq)? : command
syntax "prove_postcondition_decidable_for " ident (" by " tacticSeq)? : command
syntax "prove_signals_decidable_for " ident (" by " tacticSeq)? : command
syntax "#derive_tester_for " ident : command

private meta def deriveDecisions (name : Ident) (kind suffix : Name)
    (proof? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : CommandElabM Unit := do
  let resolved ← liftTermElabM <| decisionName name suffix
  let declId := mkIdentFrom name (`_root_ ++ resolved)
  let kindId := mkIdent kind
  let proof := proof?.getD (← `(tacticSeq|
    all_goals (infer_aux_decidable_with_heuristics; infer_instance)))
  let cmd ← `(command|
    public def $declId : testing_decision_type% $name $kindId := by
      prepare_testing_decisions
      all_goals (simp only [Named.mk, Lean.Order.ofProp_prop_eq, Lean.Order.meet])
      ($proof))
  elabCommand cmd

elab_rules : command
  | `(prove_precondition_decidable_for $name:ident $[by $proof]?) =>
    deriveDecisions name `pre `preDecidable proof
  | `(prove_postcondition_decidable_for $name:ident $[by $proof]?) =>
    deriveDecisions name `post `postDecidable proof
  | `(prove_signals_decidable_for $name:ident $[by $proof]?) =>
    deriveDecisions name `signals `signalsDecidable proof
  | `(#derive_tester_for $name:ident) => do
    for (kind, suffix) in [(`pre, `preDecidable), (`post, `postDecidable),
        (`signals, `signalsDecidable)] do
      let resolved ← liftTermElabM <| decisionName name suffix
      unless (← getEnv).contains resolved do
        deriveDecisions name kind suffix none
    let resolved ← liftTermElabM <| decisionName name `check
    let declId := mkIdentFrom name (`_root_ ++ resolved)
    elabCommand (← `(command| public def $declId := testing_checker% $name))

end Velvet.Testing
