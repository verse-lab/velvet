import Auto
import Lean
import Lean.Parser

import Loom.MonadAlgebras.WP.Attr
import Loom.MonadAlgebras.WP.Tactic
-- import Loom.MonadAlgebras.WP.DoNames'
import Loom.MonadAlgebras.WP.Gen
-- import Loom.Tactic
import Loom.TacticAsync
import Loom.SMT

import CaseStudies.Extension
import CaseStudies.Macro

import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta

private def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimplePersistentEnvExtension.get [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

/-- Get assertion info: returns (name, syntax) pair for case tagging -/
def getAssertionInfo : TacticM (Option (Name × Term)) := withMainContext do
  let goal <- getMainTarget
  let goalStx <- ppExpr goal
  let ⟨_, ss, ns, _⟩ <- loomAssertionsMap.get
  let .some withNameExpr := goal.find? (fun e => e.isAppOf ``WithName)
    | let .some typeWithNameExpr := goal.find? (fun e => e.isAppOf ``typeWithName)
        | throwError s!"Failed to parse an assertion without names: {goalStx}"
      let nname := typeWithNameExpr.getAppArgs[2]!
      let sname <- nname.getName
      let some id1 := ns[sname]?
        | throwError s!"typeWithName {sname} not registered: {typeWithNameExpr}"
      return some (sname, ss[id1]!)
  match_expr withNameExpr with
  | WithName exp name =>
    let name <- name.getName
    let some id := ns[name]?
      | let .some typeWithNameExpr := exp.find? (fun e => e.isAppOf ``typeWithName)
          | throwError s!"Failed to prove assertion without names: {goalStx}"
        let nname := typeWithNameExpr.getAppArgs[2]!
        let sname <- nname.getName
        let some id1 := ns[sname]?
          | throwError s!"typeWithName {sname} not registered: {typeWithNameExpr}"
        return some (sname, ss[id1]!)
    return some (name, ss[id]!)
  | _ => throwError s!"Failed to prove assertion which is not registered4: {goalStx}"

def getAssertionStx : TacticM (Option Term) := do
  let info? <- getAssertionInfo
  return info?.map (·.2)

declare_syntax_cat loom_solve_tactic
syntax "loom_solve" : loom_solve_tactic
syntax "loom_solve_async" (num)? : loom_solve_tactic
syntax "loom_solve_async!" (num)? : loom_solve_tactic
syntax "loom_solve?" : loom_solve_tactic
syntax "loom_solve!" : loom_solve_tactic
syntax loom_solve_tactic : tactic

syntax "loom_goals_intro" : tactic
syntax "loom_unfold" : tactic
syntax "loom_auto" : tactic
syntax "loom_solver" : tactic

def loomSolveAsync? : TSyntax `loom_solve_tactic -> Option (Option Nat)
  | `(loom_solve_tactic| loom_solve_async $n ?)
  | `(loom_solve_tactic| loom_solve_async! $n ?) => some (n.map (·.getNat))
  | _ => none

def loomSolveIsReporting : TSyntax `loom_solve_tactic -> Bool
  | `(loom_solve_tactic| loom_solve_async! $_ ?)
  | `(loom_solve_tactic| loom_solve!) => true
  | _ => false

elab_rules : tactic
  | `(tactic| loom_goals_intro) => withMainContext do
    let vlsIntro <- `(tactic| (
      repeat' loom_intro
      wpgen
      try simp only [loomWpSimp]
      try unfold spec
      try simp only [invariantSeq]
      try simp only [WithName.mk']
      try simp only [WithName.erase]
      try simp only [typeWithName.erase]
      try simp only [List.foldr]
      try simp only [loomLogicSimp]
      try simp only [iSup_apply, iSup_Prop_eq, exists_and_left, exists_and_right,
                     iInf_apply, iInf_Prop_eq, forall_and_left, forall_and_right]
      repeat loom_intro
      repeat' (loom_split <;> (repeat loom_intro))))
    evalTactic vlsIntro

elab_rules : tactic
  | `(tactic| loom_unfold) => withMainContext do
    let vlsUnfold <- `(tacticSeq|
      all_goals try unfold WithName at *
      all_goals try unfold typeWithName at *
      all_goals try unfold MProdWithName)
    evalTactic vlsUnfold

elab_rules : tactic
  | `(tactic| loom_auto) => withMainContext do
    let ctx := (<- solverHints.get)
    let mut hints : Array (TSyntax ``Auto.hintelem) := #[]
    for c in ctx do
      hints := hints.push $ <- `(Auto.hintelem| $(mkIdent c):ident)
    hints := hints.push $ <- `(Auto.hintelem| *)
    let vlsAuto <- `(tactic| try (try simp only [loomAbstractionSimp] at *); loom_smt [$hints,*])
    evalTactic vlsAuto

elab_rules : tactic
  | `(tactic| $vls:loom_solve_tactic) => withMainContext do
    let vlsTryThis <- `(tacticSeq|
        loom_goals_intro
        loom_unfold
        loom_solver)
    if let `(loom_solve_tactic| loom_solve?) := vls then
      Tactic.TryThis.addSuggestion (<-getRef) vlsTryThis
    else
      let vlsIntro ← `(tactic| loom_goals_intro)
      let vlsUnfold ← `(tactic| loom_unfold)
      let vlsSolve ← `(tactic| try solve | loom_unfold; loom_solver)
      evalTactic vlsIntro
      let goals <- getUnsolvedGoals
      if let some n := loomSolveAsync? vls then
        if goals.length < n.getD 0 then
          logWarningAt vls m!"This method has only {goals.length} Verification Conditions, but `loom_solve_async` is called with {n.get!} asynchronous tasks"
        allGoalsAsync (numTasks := n.map (·.min goals.length)) do
          evalTactic vlsSolve
        logWarningAt vls m!
        "`loom_solve_async` uses sorry to admit all the solved goals for now, consider running `loom_solve` once proof is complete to get the proof term"
      else
        allGoals do evalTactic vlsSolve
      let mut unsolved := #[]
      for mvarId in <- getUnsolvedGoals do
        setGoals [mvarId]
        let info? <- getAssertionInfo
        evalTactic vlsUnfold
        if let some (name, stx) := info? then
          -- Combine the internal name with the expression for readable case tags
          let exprStr := stx.raw.prettyPrint.pretty
          let caseTag := s!"{name}: {exprStr}"
          (<- getMainGoal).setTag <| .mkSimple caseTag
          if loomSolveIsReporting vls then
            logErrorAt stx $ m!"Failed to prove assertion\n{mvarId}"
        else if loomSolveIsReporting vls then
          logErrorAt vls m!"Failed to prove nameless assertion\n{mvarId}"
        unsolved := unsolved.append (← getUnsolvedGoals).toArray
      setGoals unsolved.toList

elab "loom_solve?" : tactic => withMainContext do
  let ctx := (<- solverHints.get)
  let mut hints : Array (TSyntax ``Auto.hintelem) := #[]
  for c in ctx do
    hints := hints.push $ <- `(Auto.hintelem| $(mkIdent c):ident)
  -- hints := hints.push $ <- `(Auto.hintelem| *)
  let tac <- `(tactic| (
  intro
  try simp only [$(mkIdent `loomAbstractionSimp):ident] at *
  wpgen
  try simp only [$(mkIdent `loomWpSimp):ident]
  try simp only [$(mkIdent ``WithName):ident]
  try simp only [$(mkIdent ``typeWithName):ident]
  try unfold spec
  try simp only [$(mkIdent ``invariantSeq):ident]
  try simp only [$(mkIdent ``WithName.mk'):ident]
  try simp only [$(mkIdent ``WithName.erase):ident]
  try simp only [$(mkIdent ``typeWithName.erase):ident]
  try simp only [$(mkIdent ``List.foldr):ident]
  try simp only [$(mkIdent `loomLogicSimp):ident]
  try simp only [$(mkIdent `simpMAlg):ident]
  repeat' (apply $(mkIdent ``And.intro) <;> (repeat loom_intro))
  any_goals loom_smt [$hints,*]
  ))
  Tactic.TryThis.addSuggestion (<-getRef) tac

elab_rules : tactic
  | `(tactic| loom_solver) => withMainContext do
    let opts <- getOptions
    let solver := opts.getString (defVal := "grind") `loom.solver
    match solver with
      | "grind" =>
        /- In case of `grind` solver, we need  to fetch the number of splits from the options first. -/
        let splits := Lean.Syntax.mkNatLit <| (opts.getNat (defVal := 20) `loom.solver.grind.splits)
        evalTactic $ <- `(tactic| grind ($(mkIdent `splits):ident := $splits))
      | "custom" =>
        evalTactic $ <- `(tactic| fail "Custom solver is not specified")
      | _ => evalTactic $ <- `(tactic| loom_auto)
