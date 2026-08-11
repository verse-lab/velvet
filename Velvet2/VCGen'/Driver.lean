/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Meta
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Velvet2.VCGen'.Solve
public import Velvet2.Named
public import Lean.Meta.Sym.Grind

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.SpecAttr

namespace Lean.Elab.Tactic.Do.Internal

/-!
Worklist driver for `vcgen`. Wraps `solve` with a queue of pending goals
and emits VCs (or invariant holes) for those `solve` cannot decompose further.
-/

namespace VCGen'

open _root_.Lean.Elab.Tactic.Do.Internal.VCGen

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
  let target ← instantiateMVars (← mv.getType)
  trace[Elab.Tactic.Do.vcgen] "🧩 inv{n}: looking for a user invariant for:\n   {target}"
  try
    let some alt := invariantAlts[n]? | do
      trace[Elab.Tactic.Do.vcgen] "   inv{n}: no matching user alternative"
      return false
    let tac ← match alt with
      | `(Lean.Parser.Tactic.invariantDotAlt| · $rhs) =>
          trace[Elab.Tactic.Do.vcgen] "   inv{n}: found positional alternative `· {rhs}`"
          `(tactic| exact $rhs)
      | `(Lean.Parser.Tactic.invariantCaseAlt| | $tag $args* => $rhs) =>
          trace[Elab.Tactic.Do.vcgen] "   inv{n}: found labelled alternative `| {tag} ... => {rhs}`"
          `(tactic| (rename_i $args*; exact $rhs))
      | _ =>
          trace[Elab.Tactic.Do.vcgen] "   inv{n}: alternative has an unexpected syntax shape"
          return false
    -- `withDefault`: the surrounding grind context forces reducible transparency,
    -- under which the invariant's binder type (e.g. `List.Cursor _`) isn't
    -- resolved enough for term elaboration of `xs.suffix.length` to succeed.
    trace[Elab.Tactic.Do.vcgen] "   inv{n}: elaborating the alternative with `exact`"
    withRef alt <| discard <| Meta.withDefault <| Lean.Elab.runTactic mv tac {} {}
    -- The tactic runs without throwing even when it fails to close the goal;
    -- check explicitly that the MVar got assigned.
    if ← mv.isAssigned then
      -- Preprocess the assignment to `mv` because it will interact with the `SymM` world
      if let some val ← getExprMVarAssignment? mv then
        let val ← unfoldReducible val
        let val ← shareCommon val
        mv.assign val
        trace[Elab.Tactic.Do.vcgen] "   ✓ inv{n} assigned to:\n      {val}"
      else
        trace[Elab.Tactic.Do.vcgen] "   ✓ inv{n} assigned"
      return true
    else
      trace[Elab.Tactic.Do.vcgen] "   ✗ inv{n}: `exact` left the invariant goal open"
      return false
  catch ex =>
    trace[Elab.Tactic.Do.vcgen] "   ✗ inv{n}: elaboration failed:\n      {ex.toMessageData}"
    return false

/-- Pull invariant subgoals out of `subgoals` and handle them eagerly: register
each in `State.invariants` (1-based stable index) and try to inline-elaborate
its matching user alt. Returns the remaining non-invariant subgoals for `work`
to enqueue. Eager handling here ensures dependent VCs see `?inv` assigned by
the time they reach `emitVC`. -/
private def handleInvariantSubgoals (subgoals : List MVarId) : VCGenM (Array MVarId) := do
  let env ← getEnv
  let mut others : Array MVarId := #[]
  for sg in subgoals do
    let target ← instantiateMVars (← sg.getType)
    if isSpecInvariantType env target then
      let n := (← get).invariants.size + 1
      trace[Elab.Tactic.Do.vcgen]
        "🧩 Detected invariant subgoal inv{n}; removing it from the ordinary VC worklist:\n   {target}"
      modify fun s => { s with invariants := s.invariants.push sg }
      trace[Elab.Tactic.Do.vcgen] "   inv{n}: registered in `State.invariants`"
      if ← elabInvariant (← read).invariantAlts n sg then
        modify fun s => { s with inlineHandledInvariants := s.inlineHandledInvariants.insert n }
        trace[Elab.Tactic.Do.vcgen]
          "   inv{n}: handled eagerly; dependent VCs will see its assignment"
      else
        sg.setKind .syntheticOpaque
        trace[Elab.Tactic.Do.vcgen]
          "   inv{n}: still open; marked `syntheticOpaque` so unification cannot guess it"
    else
      trace[Elab.Tactic.Do.vcgen] "➡ Ordinary VC subgoal; enqueueing:\n   {target}"
      others := others.push sg
  return others

/-- Proof-producing rewrite rules used only after VCGen has stopped structurally decomposing a
VC. The first group pushes lattice operations through predicate application; the second translates
the resulting `Prop` lattice into ordinary logical syntax. -/
private def emittedLatticeSimpRules : Array Name := #[
  ``Lean.Order.meet_apply,
  ``Lean.Order.join_apply,
  ``Lean.Order.himp_apply,
  ``Lean.Order.top_apply,
  ``Lean.Order.bot_apply,
  ``Lean.Order.CompleteLattice.ofProp_apply,
  ``Lean.Order.iInf_apply,
  ``Lean.Order.iSup_apply,
  ``Lean.Order.meet_prop_eq_and,
  ``Lean.Order.join_prop_eq_or,
  ``Lean.Order.himp_prop_eq_imp,
  ``Lean.Order.top_prop_eq,
  ``Lean.Order.bot_prop_eq,
  ``Lean.Order.ofProp_prop_eq,
  ``Lean.Order.iInf_prop_eq_forall,
  ``Lean.Order.iSup_prop_eq_exists,
  ``Lean.Order.le_prop_eq_imp
]

private def simplifyLatticePasses (ctx : Meta.Simp.Context) (goal : MVarId) :
    Nat → MetaM (Option MVarId)
  | 0 => pure (some goal)
  | fuel + 1 => goal.withContext do
      let (result, _) ← simpGoal goal ctx
        (fvarIdsToSimp := (← getLCtx).getFVarIds)
      match result with
      | none => return none
      | some (_, goal) => simplifyLatticePasses ctx goal fuel

/-- Simplify lattice syntax in a final emitted VC and all of its actual local hypotheses, then
split structural conjunctions of named hypotheses. This runs after the solver no longer needs the
outer entailment structure. Named target conjunctions are split separately with a symbolic backward
rule so the resulting goals can share their Grind state. -/
private def simplifyLatticeVC (goal : MVarId) : VCGenM (List MVarId) := do
  -- Consume annotations that are already exposed, then run the same pass again for annotations
  -- exposed by the lattice rewrites.
  let goals ← Named.processHyp goal
  goals.flatMapM fun goal => goal.withContext do
    let mut theorems : SimpTheorems := {}
    for declName in emittedLatticeSimpRules do
      theorems ← theorems.addConst declName
    let ctx ← Simp.mkContext
      (config := { failIfUnchanged := false })
      (simpTheorems := #[theorems])
    -- Application rewrites can expose new proposition-level lattice redexes at the root. A small
    -- bounded fixed-point pass handles function lattices without enabling these rules globally.
    let some goal ← simplifyLatticePasses ctx goal 4 | return []
    Named.processHyp goal

/-- Remove an outer `Named.mk` from a goal using the symbolic simplifier. This is run only after
all VC generation and trivial-conjunct processing has finished. -/
private def unwrapNamedGoal (goal : Grind.Goal) : SymM (Option Grind.Goal) := do
  let thm ← Sym.Simp.mkTheoremFromDecl ``Named.mk_eq
  let mut theorems : Sym.Simp.Theorems := {}
  theorems := theorems.insert thm
  let methods : Sym.Simp.Methods := { post := theorems.rewrite }
  match ← Sym.simpGoal goal.mvarId methods with
  | .closed => return none
  | .noProgress =>
      throwError "Failed to unwrap named goal {goal.mvarId}"
  | .goal mvarId =>
      return some { goal with mvarId }

/-- Split structural conjunctions of separately named target propositions using VCGen's symbolic
`And.intro` rule. Structure inside one `Named.mk` remains one obligation. -/
private partial def splitNamedGoalConjs (goal : Grind.Goal) : VCGenM (List Grind.Goal) :=
    goal.mvarId.withContext do
  let target ← Sym.shareCommon (<- goal.mvarId.getType')
  if Option.isSome (← Named.extract? target) then
    return [goal]
  if target.isForall then
    let .goal _ mvarId ← Sym.intros goal.mvarId | return [goal]
    let goal ← processHypotheses { goal with mvarId }
    return ← splitNamedGoalConjs goal
  if target.isAppOfArity ``And 2
      && Named.contains (target.getArg! 0) && Named.contains (target.getArg! 1) then
    let .goals subgoals ← (← read).backwardRules.andIntro.apply goal.mvarId
      | throwError "Failed to split named conjunction in {goal.mvarId}"
    return ← subgoals.flatMapM fun mvarId =>
      splitNamedGoalConjs { goal with mvarId }
  return [goal]

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
Invariant subgoals are handled separately by `handleInvariantSubgoals` directly inside `work`,
so they never reach this path.
-/
public def emitVC (goal : Grind.Goal) : VCGenM Unit := do
  let baseMVarId ← elimTopPre goal.mvarId
  let baseGoal := { goal with mvarId := baseMVarId }
  let mvarIds ← simplifyLatticeVC baseMVarId
  for mvarId in mvarIds do
    -- Meta-level simplification and named-hypothesis replacement may create fresh FVarIds. Rebuild
    -- once in that case so the E-graph cannot retain references to the old local context.
    let mut goal ←
      if mvarId == baseMVarId then
        pure baseGoal
      else
        Grind.mkGoalCore mvarId
    goal ← processHypotheses goal
    if goal.inconsistent then continue
    -- Symbolic `And.intro` splitting preserves this normalized Grind state across all named leaves.
    let goals ← splitNamedGoalConjs goal
    for splitGoal in goals do
      -- `trivial`: when false, skip `solveTrivialConjuncts` (which collapses And-chains via rfl);
      -- emit the goal as-is.
      let mvarId ←
        if (← read).trivial then
          let some mvarId ← solveTrivialConjuncts splitGoal.mvarId | continue
          pure mvarId
        else
          pure splitGoal.mvarId
      mvarId.setKind .syntheticOpaque
      modify fun s => { s with vcs := s.vcs.push { splitGoal with mvarId } }

private structure WorkItem where
  goal : Grind.Goal
  scope : VCGen.Scope

public def work (scope : VCGen.Scope) (goal : Grind.Goal) : VCGenM Unit := do
  let mvarId ← preprocessMVar goal.mvarId
  let mut worklist : Array WorkItem := #[{ goal := { goal with mvarId }, scope }]
  while let some s := worklist.back? do
    worklist := worklist.pop
    let goal := s.goal
    if goal.inconsistent then continue
    match ← solve s.scope goal.mvarId with
    | .stop _reason =>
      emitVC goal
    | .goals scope subgoals =>
      -- Handle invariant subgoals eagerly here, so that VC subgoals popped
      -- from the worklist later see the invariant MVar already assigned.
      -- Non-invariant subgoals go to the worklist as usual and will eventually go through `emitVC`.
      let subgoals ← handleInvariantSubgoals subgoals
      let goal ←
        if subgoals.size > 1 then
          processHypotheses goal
        else
          pure goal
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
public partial def run (goal : Grind.Goal) (ctx : VCGen.Context) (scope : VCGen.Scope)
    (stepLimit? : Option Nat := none) (frameDB : FrameDB := {}) :
    Grind.GrindM Result := do
  let initState : VCGen.State :=
    { fuel := match stepLimit? with | some n => .limited n | none => .unlimited, frameDB }
  -- VCGen temporarily violates the `SymM` folded-projections invariant: `reduceHead?`
  -- exposes kernel projections in intermediate terms and restores the invariant in its
  -- final result, so the `shareCommon` kernel-projection check is disabled.
  let ((), state) ← Sym.withoutFoldProjsCheck <| StateRefT'.run (ReaderT.run (work scope goal) ctx) initState
  _ ← state.invariants.mapIdxM fun idx mv => do
    let curTag <- mv.getTag
    trace[Elab.Tactic.Do.vcgen] "Goal Tag: {curTag} , Goal: {mv}"
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  let vcs ← state.vcs.mapIdxM fun idx g => do
    let curTag ← g.mvarId.getTag
    let target ← instantiateMVars (← g.mvarId.getType)
    trace[Elab.Tactic.Do.vcgen] "Goal Tag: {curTag} , Goal: {g.mvarId}"
    if let some (name, _) ← Named.extract? target then
      trace[Elab.Tactic.Do.vcgen]
        "🏷 Naming vc{idx + 1} from its `Named.mk` target and unwrapping it: `{name}`"
      let some g ← SymM.run (unwrapNamedGoal g) | return none
      g.mvarId.setTag name
      return some g
    else
      let tag :=
        if curTag.isAnonymous then
          Name.mkSimple ("vc" ++ toString (idx + 1))
        else
          curTag.eraseMacroScopes
      trace[Elab.Tactic.Do.vcgen]
        "🏷 No outer `Named.mk` target; using existing/fallback tag `{tag}`"
      g.mvarId.setTag tag
      return some g
  let vcs ← vcs.filterMap id |>.filterM (not <$> ·.mvarId.isAssigned)
  let unmatchedFrames := state.frameDB.entries.filterMap fun e =>
    if e.retired then none else some e.frameStx
  return {
    invariants := state.invariants,
    vcs,
    inlineHandledInvariants := state.inlineHandledInvariants,
    unmatchedFrames }

end VCGen'

end Lean.Elab.Tactic.Do.Internal
