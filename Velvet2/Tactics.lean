import Velvet2.VCGen.Frontend

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
`vcgen_`: repeatedly `split at *`, destruct conjunctive hypotheses, and construct
conjunctive goals. It also prunes immediate contradiction branches created by
the splits.
-/
elab "split_conjs" : tactic => do
  evalTactic (← `(tactic| repeat' split at *))
  evalTactic (← `(tactic| all_goals try contradiction))
  let goals ← getGoals
  let goals ← liftMetaM <| goals.flatMapM fun goal => do
    (← splitAndHyps goal).flatMapM splitAndGoals
  setGoals goals
  evalTactic (← `(tactic| all_goals try contradiction))
