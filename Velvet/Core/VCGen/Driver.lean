/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Meta
public import Lean.Elab.Tactic.VCGen.Context
public import Velvet.Core.VCGen.Solve
public import Velvet.Core.VCGen.Util
public import Velvet.Core.Named
public import Lean.Meta.Sym.Grind
public import Lean.Meta.Sym.InstantiateMVarsS

open Lean Meta Elab Tactic Sym Sym.Internal Lean.Order
open Lean.Elab.Tactic.Do.SpecAttr
open Lean.Elab.Tactic.VCGen
open VCGen

namespace VCGen

/-!
Worklist driver for `vcgen`. Wraps `solve` with a queue of pending goals
and emits VCs (or invariant holes) for those `solve` cannot decompose further.
-/


/--
Try to elaborate the user's invariant alt for invariant number `n` inline,
discharging `mv` if successful. Looks up `Context.invariantAlts[n]?` (pre-parsed
in `Frontend`) and dispatches to `exact $rhs` for bullet form or
`rename_i $args*; exact $rhs` for labelled form. Returns whether elaboration
succeeded. Numbering is 1-based; out-of-order labelled forms (e.g. `| inv2 => …`
before `| inv1 => …`) are supported because the map is keyed by parsed number,
not position.
-/
public def elabInvariant (invariantAlts : Std.HashMap Nat Syntax) (n : Nat) (mv : MVarId) : SymM Bool := do
  try
    let some alt := invariantAlts[n]? | return false
    let tac ← match alt with
      | `(Lean.Parser.Tactic.invariantDotAlt| · $rhs) => `(tactic| exact $rhs)
      | `(Lean.Parser.Tactic.invariantCaseAlt| | $_tag $args* => $rhs) =>
          `(tactic| (rename_i $args*; exact $rhs))
      | _ => return false
    -- `withDefault`: the surrounding grind context forces reducible transparency,
    -- under which the invariant's type isn't resolved enough for term elaboration
    -- of the alternative's right-hand side to succeed.
    withRef alt <| discard <| Meta.withDefault <| Lean.Elab.runTactic mv tac {} {}
    -- The tactic runs without throwing even when it fails to close the goal;
    -- check explicitly that the MVar got assigned.
    if ← mv.isAssigned then
      -- Preprocess the assignment to `mv` because it will interact with the `SymM` world
      if let some val ← getExprMVarAssignment? mv then
        let val ← unfoldReducible val
        let val ← shareCommon val
        mv.assign val
      return true
    else
      return false
  catch _ => return false

/-- Pull invariant subgoals out of `subgoals` and handle them eagerly: register
each in `State.invariants` (1-based stable index) and try to inline-elaborate
its matching user alt. Returns the remaining non-invariant subgoals for `work`
to enqueue. Eager handling here ensures dependent VCs see `?inv` assigned by
the time they reach `emitVC`. -/
private def handleInvariantSubgoals (subgoals : List MVarId) : VCGenM (Array MVarId) := do
  let env ← getEnv
  let mut others : Array MVarId := #[]
  for sg in subgoals do
    if isSpecInvariantType env (← sg.getType) then
      let n := (← get).invariants.size + 1
      modify fun s => { s with invariants := s.invariants.push sg }
      if ← elabInvariant (← read).invariantAlts n sg then
        modify fun s => { s with inlineHandledInvariants := s.inlineHandledInvariants.insert n }
      else
        sg.setKind .syntheticOpaque
    else
      others := others.push sg
  return others

private def simpDecls : Array Name := #[``Named.mk_eq]

private def mkNamedSimpMethods : MetaM Sym.Simp.Methods := do
  let mut theorems : Sym.Simp.Theorems := {}
  for declName in simpDecls do
    theorems := theorems.insert (← Sym.Simp.mkTheoremFromDecl declName)
  return { post := theorems.rewrite }

/-- If the target is an outer internal named atom (possibly behind assigned metavariables or at the head
of an application), unwrap it with the symbolic simplifier and install its name as the goal tag.
Returns the original goal when it is not named, and `none` when simplification closes it. -/
private def processNamedGoal (goal : Grind.Goal) : SymM (Option Grind.Goal) := do
  let rawTarget ← goal.mvarId.getType
  let target ← instantiateMVarsS rawTarget
  let some info ← Named.extractInfo? target | return some goal
  let name := info.name
  -- Refresh the metavariable itself, then simplify that exact target. Simplifying `target`
  -- separately and attaching its equality proof to the old raw target can leak context-local fvars.
  let mvarId ← preprocessMVar goal.mvarId
  let mvarId ← match ← Sym.simpGoal mvarId (← mkNamedSimpMethods) with
  | .closed => return none
  | .noProgress => pure mvarId
  | .goal mvarId => pure mvarId
      -- Removing `Named.mk` can expose a fresh beta-redex when a named StateT/ReaderT
      -- assertion is applied to its state/environment arguments. The worklist's final
      -- normalization ran before this unwrapping, so normalize the exposed target once
      -- more while retaining the inherited Grind state.
      let mvarId ← match ← Sym.simpGoal mvarId
          (← mkGeneratedControlSimpMethods) with
        | .closed => return none
        | .noProgress => pure mvarId
        | .goal mvarId => pure mvarId
      let mvarId ← match info.source? with
        | none => pure mvarId
        | some source =>
            let target ← mvarId.getType
            mvarId.replaceTargetDefEqFast (Named.annotateSourceRef target source)
      mvarId.setTag name
      return some { goal with mvarId }

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
Invariant subgoals are handled separately by `handleInvariantSubgoals` directly inside `work`,
so they never reach this path.
-/
public def emitVC (goal : Grind.Goal) : VCGenM Unit := do
  let mut goal := { goal with mvarId := ← elimTopPre goal.mvarId }
  goal ← processHypotheses goal
  let some mvarId ← cleanupVC goal.mvarId | return
  let some emittedGoal ← processNamedGoal { goal with mvarId } | return
  let some mvarId ← cleanupVC emittedGoal.mvarId | return
  let emittedGoal := { emittedGoal with mvarId }
  emittedGoal.mvarId.setKind .syntheticOpaque
  modify fun s => { s with vcs := s.vcs.push emittedGoal }

private structure WorkItem where
  goal : Grind.Goal
  scope : Scope

public def work (scope : Scope) (goal : Grind.Goal) : VCGenM Unit := do
  let mvarId ← preprocessMVar goal.mvarId
  let mut worklist : Array WorkItem := #[{ goal := { goal with mvarId }, scope }]
  while let some s := worklist.back? do
    worklist := worklist.pop
    if ← s.goal.mvarId.isAssigned then continue
    let goal ← processHypotheses s.goal
    if goal.inconsistent then continue
    match ← solve s.scope goal.mvarId with
    | .stop _reason =>
      -- `solve` has finished decomposing everything it recognizes. Before emitting a
      -- verification condition, clear any remaining *concrete* control flow that the
      -- do-elaborator generated for loops (branch guards, tuple projections). If that
      -- simplification exposes a connective `solve` can split, put the goal back on the
      -- worklist so the split happens now; otherwise the goal is genuinely stuck and is
      -- emitted as a VC.
      match ← Sym.simpGoal goal.mvarId (← mkGeneratedControlSimpMethods) with
      | .closed => continue
      | .noProgress => emitVC goal
      | .goal mvarId =>
          worklist := worklist.push { goal := { goal with mvarId }, scope := s.scope }
    | .goals scope subgoals =>
      -- Handle invariant subgoals eagerly here, so that VC subgoals popped
      -- from the worklist later see the invariant MVar already assigned.
      -- Non-invariant subgoals go to the worklist as usual and will eventually go through `emitVC`.
      let subgoals ← handleInvariantSubgoals subgoals
      worklist := worklist ++ subgoals.reverse.map (fun mv =>
        { goal := { goal with mvarId := mv }, scope })

public structure Result where
  /-- All invariant goals emitted during VC generation, in emit order. The MVarId at
  index `i` carries tag `inv{i+1}`, so callers can treat the array index as the
  invariant number. Some entries may already be assigned (inline-elaborated by
  `Driver.emitVC`); the caller is responsible for filtering before discharging. -/
  invariants : Array MVarId
  /-- Unassigned VCs. Each shares the parent `Grind.Goal`'s state. -/
  vcs : Array Grind.Goal
  /-- Invariant numbers handled inline by `Driver.emitVC`. Used by `Frontend` to
  avoid spurious "alt does not match any invariant" warnings for inline-consumed
  alts. -/
  inlineHandledInvariants : Std.HashSet Nat := {}
  /-- Frame terms of `frames` alternatives whose program pattern matched no program. -/
  unmatchedFrames : Array Syntax := #[]

/--
Generate verification conditions for a goal of the form `pre ⊑ wp e post epost s₁ ... sₙ` by repeatedly
decomposing `e` using registered `@[spec]` theorems.
Return the VCs and invariant goals.

`stepLimit?`, when `some n`, seeds the fuel counter to `n`; when `none`, fuel is unlimited.
-/
public partial def run (goal : Grind.Goal) (ctx : Lean.Elab.Tactic.VCGen.Context) (scope : Scope)
    (stepLimit? : Option Nat := none) (frameDB : FrameDB := {}) :
    Grind.GrindM Result := do
  let initState : Lean.Elab.Tactic.VCGen.State :=
    { fuel := match stepLimit? with | some n => .limited n | none => .unlimited, frameDB }
  -- VCGen temporarily violates the `SymM` folded-projections invariant: `reduceHead?`
  -- exposes kernel projections in intermediate terms and restores the invariant in its
  -- final result, so the `shareCommon` kernel-projection check is disabled.
  let ((), state) ← Sym.withoutFoldProjsCheck <| StateRefT'.run (ReaderT.run (work scope goal) ctx) initState
  _ ← state.invariants.mapIdxM fun idx mv => do
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  _ ← state.vcs.mapIdxM fun idx g => do
    let currentTag ← g.mvarId.getTag
    let tag :=
      if currentTag.isAnonymous then
        Name.mkSimple ("vc" ++ toString (idx + 1))
      else
        currentTag.eraseMacroScopes
    g.mvarId.setTag tag
  let vcs ← state.vcs.filterM (not <$> ·.mvarId.isAssigned)
  let unmatchedFrames := state.frameDB.entries.filterMap fun e =>
    if e.retired then none else some e.frameStx
  return {
    invariants := state.invariants,
    vcs,
    inlineHandledInvariants := state.inlineHandledInvariants,
    unmatchedFrames }


end VCGen
