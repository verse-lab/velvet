import Lean

open Lean Meta Elab Tactic

namespace Velvet2.Tactic

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

end Velvet2.Tactic

/--
`split_conjs` performs the cheap structural cleanup that often appears after
`vcgen`: repeatedly `split at *`, destruct conjunctive hypotheses, and construct
conjunctive goals. It also prunes immediate contradiction branches created by
the splits.

It intentionally does not call heavier automation such as `grind`; use it as a
normalizer before the domain-specific discharge step.
-/
elab "split_conjs" : tactic => do
  evalTactic (← `(tactic| repeat' split at *))
  evalTactic (← `(tactic| all_goals try contradiction))
  let goals ← getGoals
  let goals ← liftMetaM <| goals.flatMapM fun goal => do
    (← Velvet2.Tactic.splitAndHyps goal).flatMapM
      Velvet2.Tactic.splitAndGoals
  setGoals goals
  evalTactic (← `(tactic| all_goals try contradiction))

syntax "vcgen' " "[" term,* "]" (" with " ident)? : tactic

elab "vcgen' " "[" _args:term,* "]" _with:(" with " ident)? : tactic => do
  evalTactic (← `(tactic| skip))
