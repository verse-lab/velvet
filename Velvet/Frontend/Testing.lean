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
    let_expr Std.Internal.Do.Triple _ _ _ _ _ _ program wpInst pre post signals := body
      | throwError "expected a method Triple, got {body}"
    k args program wpInst pre post signals

/-- Expand only the decision structure, preserving the propositions and their binder names. -/
private meta partial def decisionType (p : Expr) : TermElabM Expr := do
  let type ← whnf (← inferType p)
  if type.isProp then
    return ← mkAppM ``Decidable #[p]
  match type with
  | .forallE name domain _ bi =>
    withLocalDecl name bi domain fun arg => do
      mkForallFVars #[arg] (← decisionType (mkApp p arg))
  | _ =>
    if type.isAppOf ``Std.Internal.Do.EPost.Cons then
      return ← mkAppM ``Prod #[← decisionType (mkProj ``Std.Internal.Do.EPost.Cons 0 p),
        ← decisionType (mkProj ``Std.Internal.Do.EPost.Cons 1 p)]
    if type.isAppOf ``Prod then
      return ← mkAppM ``Prod #[← decisionType (mkProj ``Prod 0 p),
        ← decisionType (mkProj ``Prod 1 p)]
    if type.isConstOf ``Std.Internal.Do.EPost.Nil then return mkConst ``Unit
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
    let contractWP ← mkAppOptM ``Std.Internal.Do.WP.wp #[none, none, none, none, none, none,
      some wpInst, some program, some post, some signals]
    let expected ← mkAppM ``PointwiseDecidable #[contractWP]
    unless ← isDefEq (← inferType wpDec) expected do
      throwErrorAt name "DecidableWP does not match this method's WP interpretation"
    -- The elaborated assertion type is selected by the WP instance for the monad stack.
    -- Follow its entire telescope, including state/environment arguments absent in source clauses.
    forallTelescopeReducing (← inferType pre) fun context leaf => do
      unless leaf.isProp do throwError "tester assertions must end in Prop"
      let pre := mkAppN pre context
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
