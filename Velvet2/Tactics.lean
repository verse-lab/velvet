import Lean
import Std.Tactic.Do
import Velvet2.Named

open Lean Meta Elab Tactic

private def isAndType (type : Expr) : MetaM Bool := do
  let type ← whnfR (← instantiateMVars type)
  return type.isAppOfArity ``And 2

private partial def splitAndHyps (goal : MVarId) : MetaM (List MVarId) := do
  goal.withContext do
    for localDecl in ← getLCtx do
      if localDecl.isImplementationDetail then
        continue
      if ← isAndType localDecl.type then
        let subgoals ← goal.cases localDecl.fvarId
        return (← subgoals.toList.flatMapM fun subgoal =>
          splitAndHyps subgoal.mvarId)
    return [goal]

private partial def splitAndGoals (goal : MVarId) : MetaM (List MVarId) := do
  goal.withContext do
    if ← isAndType (← goal.getType) then
      return (← (← goal.constructor).flatMapM splitAndGoals)
    return [goal]

/--
`split_conjs` performs the cheap structural cleanup that often appears after
`vcgen`: repeatedly `split at *`, destruct conjunctive hypotheses, and construct
conjunctive goals. It also prunes immediate contradiction branches created by
the splits.
-/
elab "split_conjs" : tactic => do
  evalTactic (← `(tactic| repeat' split at *))
  evalTactic (← `(tactic| all_goals try contradiction))
  let goals ← getGoals
  let goals ← liftMetaM <| goals.flatMapM fun goal => do
    (← splitAndHyps goal).flatMapM
      splitAndGoals
  setGoals goals
  evalTactic (← `(tactic| all_goals try contradiction))

syntax "vcgen' " "[" term,* "]" (" with " ident)? : tactic

private partial def processNamedGoals (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    let target ← goal.getType
    if let some target ← withReducible <| reduceRecMatcher? target then
      return ← processNamedGoals (← goal.replaceTargetDefEq target)

    match ← Named.processGoal goal with
    | [processed] =>
        if processed != goal then
          return ← processNamedGoals processed
        let target ← whnfR (← instantiateMVars target)
        if target.isAppOfArity ``And 2 && Named.contains target then
          return ← (← goal.constructor).flatMapM processNamedGoals
        return [goal]
    | processed =>
        return ← processed.flatMapM processNamedGoals

private def normalizePropLattice (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    let mut theorems : SimpTheorems := {}
    theorems ← theorems.addConst ``Lean.Order.meet_prop_eq_and
    theorems ← theorems.addConst ``Lean.Order.ofProp_prop_eq
    let ctx ← Simp.mkContext
      (config := { failIfUnchanged := false })
      (simpTheorems := #[theorems])
    let (result, _) ← simpGoal goal ctx
      (fvarIdsToSimp := (← getLCtx).getFVarIds)
    match result with
    | none => return []
    | some (_, goal) => return [goal]

private def processNamedVCs (goals : List MVarId) : MetaM (List MVarId) := do
  let goals ← goals.flatMapM normalizePropLattice
  let goals ← goals.flatMapM Named.processHyp
  goals.flatMapM processNamedGoals

/--
Expose names that became reachable after simplifying or splitting matches.
Named hypotheses are unwrapped and renamed; named conjunctions of verification
conditions are split; named targets are unwrapped and assigned matching case
tags.
-/
elab "name_vcs" : tactic => do
  setGoals (← liftMetaM <| processNamedVCs (← getGoals))

elab "vcgen' " "[" args:term,* "]" _with:(" with " ident)? : tactic => do
  let simpArgs ← args.getElems.mapM fun arg =>
    `(Lean.Parser.Tactic.simpLemma| $arg:term)
  evalTactic (← `(tactic| vcgen [$(Syntax.TSepArray.ofElems simpArgs),*]))
  setGoals (← liftMetaM <| processNamedVCs (← getGoals))
