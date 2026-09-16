module

public meta import Velvet.Core.VCGen.Progress
public meta import Lean.Elab.Command
public meta import Lean.Server.InfoUtils
public meta import Lean.Meta.CollectMVars
public meta import Lean.Util.Sorry

open Lean Elab Meta Command Language

namespace VCGen

private meta structure ProofInfo where
  vcs : Array (ContextInfo × Syntax × VCReportInfo) := #[]
  tactics : Array (ContextInfo × TacticInfo) := #[]

private meta def collectProofInfo (infos : InfoState) : ProofInfo :=
  infos.trees.foldl (init := {}) fun acc tree =>
    tree.foldInfo (init := acc) fun ctx info acc =>
      match info with
      | .ofCustomInfo info =>
        match info.value.get? VCReportInfo with
        | some vcs => { acc with vcs := acc.vcs.push (ctx, info.stx, vcs) }
        | none => acc
      | .ofTacticInfo info => { acc with tactics := acc.tactics.push (ctx, info) }
      | _ => acc

private meta structure GoalState where
  remaining : Nat
  admitted : Bool
  recovered : Bool

private meta def inspectVC (goal : MVarId) : MetaM GoalState := do
  let proof ← instantiateMVars (mkMVar goal)
  return {
    remaining := (← getMVarsNoDelayed proof).size
    admitted := proof.hasNonSyntheticSorry
    recovered := proof.hasSyntheticSorry }

private meta def GoalState.isSolved (state : GoalState) : Bool :=
  state.remaining == 0 && !state.admitted && !state.recovered

/-- Follow the original VC through later assignments, retaining the last real state
when an unfinished tactic block has been closed by error recovery. -/
private meta def resolveVC (goal : MVarId) (initial : GoalState) (vcEnd : String.Pos.Raw)
    (tactics : Array (ContextInfo × TacticInfo)) : IO GoalState := do
  if initial.recovered || initial.admitted || initial.remaining == 0 then return initial
  for (ctx, tactic) in tactics do
    if tactic.stx.getPos?.getD 0 < vcEnd || (tactic.mctxAfter.findDecl? goal).isNone then
      continue
    let state ← { ctx with mctx := tactic.mctxAfter }.runMetaM {} (inspectVC goal)
    -- Synthetic sorry is error recovery, not a proof or an explicit admission.
    unless state.recovered do return state
  return initial

private meta def proofReports (data : ProofInfo) : IO (Array String) := do
  -- Inspect the latest committed tactic first. An enclosing tactic takes precedence
  -- over its children, which may describe a failed `try`/`first` alternative.
  let tactics := data.tactics.qsort fun (_, a) (_, b) =>
    let ae := a.stx.getTailPos?.getD 0
    let be := b.stx.getTailPos?.getD 0
    ae > be || (ae == be && a.stx.getPos?.getD 0 < b.stx.getPos?.getD 0)
  data.vcs.mapM fun (ctx, stx, vcs) => do
    let initialCtx := { ctx with mctx := vcs.mctx }
    let initialStates ← initialCtx.runMetaM {} <| vcs.goals.mapM fun (goal, _) => inspectVC goal
    let mut lines := #[]
    let mut solved := 0
    for (goal, label) in vcs.goals, initial in initialStates do
      let state ← resolveVC goal initial (stx.getTailPos?.getD 0) tactics
      let status := if state.recovered then "elaboration error"
        else if state.admitted then "admitted with sorry"
        else if state.remaining > 0 then s!"{state.remaining} remaining"
        else if initial.isSolved then "solved by velvet_vcgen"
        else "solved afterward"
      if state.isSolved then solved := solved + 1
      lines := lines.push s!"  {if state.isSolved then "✔" else "○"} {label}: {status}"
    let name := vcs.declName?.map cleanFunctionName |>.getD "proof"
    let header := if vcs.goals.isEmpty then s!"[vcgen:{name}] All VCs solved during generation."
      else s!"[vcgen:{name}] {solved}/{vcs.goals.size} VCs solved"
    return String.intercalate "\n" (header :: lines.toList)

/-- Report the resulting proof state through ordinary diagnostics. Waiting is confined to
an asynchronous task with no processing range, so earlier tactic snapshots remain usable. -/
public meta def withProofVCReport (ref : Syntax) (action : CommandElabM Unit) : CommandElabM Unit := do
  unless velvet_vcgen.showVCReport.get (← getOptions) do
    action
    return
  -- The command emits one summary; suppress the invocation-only messages inside it.
  withScope (fun scope => { scope with opts :=
    (scope.opts.setBool `velvet.collectVCReport true).setBool `velvet_vcgen.showVCReport false }) action
  let cancelTk? := (← read).cancelTk?
  let report ← wrapAsyncAsSnapshot (cancelTk? := cancelTk?) fun infos => do
    for message in ← proofReports (collectProofInfo infos) do
      logInfoAt ref message
  let task ← BaseIO.mapTask (t := (← getInfoState).substituteLazy) report
  logSnapshotTask { stx? := none, reportingRange := .skip, cancelTk?, task }

end VCGen
