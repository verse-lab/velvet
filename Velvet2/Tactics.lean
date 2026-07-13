import Lean
import Std.Tactic.Do
import Velvet2.NamedProp

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

private partial def processNamedPropGoals (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    let target ← goal.getType
    if let some target ← withReducible <| reduceRecMatcher? target then
      return ← processNamedPropGoals (← goal.replaceTargetDefEq target)

    match ← NamedProp.processNamedPropGoal goal with
    | [processed] =>
        if processed != goal then
          return ← processNamedPropGoals processed
        if ← isAndType target then
          if NamedProp.containsNamedProp target then
            return ← (← goal.constructor).flatMapM processNamedPropGoals
        return [goal]
    | processed =>
        return ← processed.flatMapM processNamedPropGoals

elab "vcgen' " "[" args:term,* "]" _with:(" with " ident)? : tactic => do
  let simpArgs ← args.getElems.mapM fun arg =>
    `(Lean.Parser.Tactic.simpLemma| $arg:term)
  evalTactic (← `(tactic| vcgen [$(Syntax.TSepArray.ofElems simpArgs),*]))
  let goals <- getGoals
  let goals ← liftMetaM <| goals.flatMapM NamedProp.processNamedPropHyp
  let goals ← liftMetaM <| goals.flatMapM processNamedPropGoals
  setGoals goals
