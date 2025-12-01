import Aesop
import Batteries.Tactic.PermuteGoals
import Batteries.Tactic.Basic
import Batteries.Data.List.Basic
import Mathlib.Data.Int.Range

import CaseStudies.Extension

import Plausible.Testable

namespace Loom.Testing

section DecidableHeuristics

section GuessingBounds

open Lean Meta Elab Tactic

/-- Gather all grounded (i.e., without loose bvars and mvars)
sub-expressions of type `ty` in `e`. A grounded expression can be
scored by `scoring` when it is an argument of an application.
`scoring` takes the function of the application and the argument index
and returns a score (the bigger the better). -/
partial def gatherClosedSubExprs (ty e : Expr) (scoring : Expr → Nat → Nat) :
  StateT (ExprMap Nat) MetaM Unit := do
  go e none
where go (e : Expr) (upper : Option (Nat × Expr))
  : StateT (ExprMap Nat) MetaM Unit := do
  match e with
  | .forallE _ d b _
  | .lam _ d b _     => go d none ; go b none
  | .letE _ t v b _  => go t none ; go v none ; go b none
  | .app ..          => e.withApp fun f args => do
    go f none
    -- let p := (f, args)
    let mut i := 0
    for arg in args do
      go arg (some (i, f))
      i := i + 1
  | .mdata _ b
  | .proj _ _ b      => go b none
  | _                => pure ()
  unless e.hasLooseBVars || e.hasMVar do
    if ← Grind.hasType e ty then
      let score := upper.elim 0 (fun (i, f) => scoring f i)
      modify fun s =>
        let oldScore := s[e]? |>.getD 0
        s.insert e (oldScore + score)

/-- Try to prove a `Subtype` goal by guessing a witness from sub-expressions
of the predicate goal with the underlying type. If `splitProd?` is true,
then for a product type, we try to find witnesses for each component
separately and combine them. Multiple scoring functions can be provided for
each component. `solver` is the tactic used to solve the predicate goal after
instantiating the witness. -/
partial def proveSubtypeByGuessing (splitProd? : Bool) (scoring : Array (Expr → Nat → Nat))
  (solver : TSyntax `tactic) : TacticM Unit := withMainContext do
  let ty ← getMainTarget
  let_expr Subtype α p := ty | throwError "the goal should be Subtype, got {ty}"
  trace[Loom.debug] "[{decl_name%}] working on Subtype {α} where {p}"
  let comps := List.toArray <| if splitProd? then splitProdType α else [α]
  -- padding the scoring functions if they are not enough
  let scoring :=
    if scoring.size ≥ comps.size then scoring
    else scoring ++ Array.replicate (comps.size - scoring.size) (fun _ _ => 0)
  let candidates ← comps.zipWithM (fun β sc => do
    let tmp ← gatherClosedSubExprs β p sc |>.run {}
    pure (β, tmp.2)) scoring
  let candidates ← mergeCandidates candidates
  let r ← tryEachCandidate α candidates solver
  unless r.isSome do
    throwError "failed find an upper bound for {p}"
where
 /-- Split a product type into its components. Note that the recursive
 call only happens on the second component due to the right associativity
 of `×`. -/
 splitProdType (α : Expr) : List Expr :=
  match α.prod? with
  | some (a, b) => a :: splitProdType b
  | none        => [α]
 mergeCandidates (sets : Array (Expr × (ExprMap Nat))) : MetaM (List Expr) :=
  match sets.back? with
  | none          => pure []
  | some (ty, s)  => do
    let tmp ← sets.pop.foldrM (init := (ty, s.toArray)) fun (tyl, s') (tyr, res) => do
      let ty' ← mkAppM ``Prod #[tyl, tyr]
      -- use the universe levels in `ty'`
      let ty' ← instantiateMVars ty'
      let lvls := ty'.getAppFn.const?.elim [] Prod.snd
      -- might choose another score merging function later
      let pairs := s'.toArray.flatMap fun (e1, score1) =>
        res.map fun (e2, score2) => (mkAppN (mkConst ``Prod.mk lvls) #[tyl, tyr, e1, e2], score1 + score2)
      pure (ty', pairs)
    -- considering both the score and the size of the expression
    let res := tmp.2.qsort fun (e1, sc1) (e2, sc2) =>
      (sc1 > sc2) || (sc1 == sc2 && e1.sizeWithoutSharing < e2.sizeWithoutSharing)
    trace[Loom.debug] "[{decl_name%}] candidates with scores: {res}"
    pure <| res.toList.map Prod.fst
 tryEachCandidate (ty : Expr) (candidates : List Expr) (solver : TSyntax `tactic) : TacticM (Option Expr) := withMainContext do
  for c in candidates do
    let r ← try
      withoutRecover do
      evalTactic (← `(tactic| refine $(mkIdent ``Subtype.mk) ?_ ?_ ))
      -- there should be two goals now
      let goals ← getGoals
      let [g1, g2] := goals | throwError "expected two goals after refining Subtype.mk, got {goals}"
      let (gnat, gp) ← do
        let tmp ← g1.getType'
        if ← isDefEq tmp ty then pure (g1, g2) else pure (g2, g1)
      gnat.assign c
      setGoals [gp]
      gp.withContext do
        evalTactic solver
      pure <| Sum.inl c
    catch ex =>
      pure <| Sum.inr ex
    match r with
    | .inl c  => return Option.some c
    | .inr ex =>
      trace[Loom.debug] "[{decl_name%}] candidate {c} failed, error:\n{ex.toMessageData}"
      pure ()
  return Option.none

/-! For now, only pre-define some simple scoring functions. -/

-- NOTE: the following does not consider even more complicated cases like
-- `¬ (a > b)`, which can be handled by preprocessing if necessary
private def scoreLELTLHSRHS (lt? smaller? : Bool) (f : Expr) (i : Nat) : Nat :=
  if let some nm := f.consumeMData.constName? then
    if ((i == 2) || (i == 3)) &&
       (if lt? then (nm == ``LT.lt || nm == ``GT.gt) else (nm == ``LE.le || nm == ``GE.ge)) then
      let b0 := smaller? ^^ (i == 2)
      let b1 := (if lt? then (nm == ``LT.lt) else (nm == ``LE.le)) ^^ b0
      if b1 then 2 else 0
    else 0
  else 0

scoped macro "prove_subtype_by_guessing_simple_solver" : tactic =>
  `(tactic| (intros ; solve | omega | grind | (simp at * ; grind)) )

scoped elab "prove_subtype_by_guessing_nat_lt" solver:tactic : tactic =>
  proveSubtypeByGuessing false #[scoreLELTLHSRHS true false] solver
scoped elab "prove_subtype_by_guessing_nat_le" solver:tactic : tactic =>
  proveSubtypeByGuessing false #[scoreLELTLHSRHS false false] solver
scoped elab "prove_subtype_by_guessing_int_lele" solver:tactic : tactic =>
  proveSubtypeByGuessing true #[scoreLELTLHSRHS false true, scoreLELTLHSRHS false false] solver

/-!
The following defines a bunch of _quasi-instances_ for deriving
`Decidable` instances that start with bounded quantifiers. They are
"quasi" since they have some non-trivial premises that cannot be
handled by the usual instance synthesis procedure.
-/

section NatBounds

variable {p : Nat → Prop} [∀ i, Decidable (p i)]

def Decidable.Nat.decidableFromBallLT (n : Nat)
  (h : (∀ i, i < n → p i) → ∀ i, p i) :
  Decidable (∀ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro h (fun h' i _ => h' i)

def Decidable.Nat.decidableFromBallLT' (h : { n : Nat // (∀ i, i < n → p i) → ∀ i, p i }) :
  Decidable (∀ i, p i) := Decidable.Nat.decidableFromBallLT h.val h.property

/-!
Note that using `decidableFromBallLE` is in general _safer_ than
using `decidableFromBallLT`. This is because if we have an upper bound `n`
for `i ≤ n`, then it also works for `i < n + 1`, while the converse is not true.

**However**, using `decidableFromBallLT` is preferred in cases like
array access.
-/

def Decidable.Nat.decidableFromBallLE (n : Nat)
  (h : (∀ i, i ≤ n → p i) → ∀ i, p i) :
  Decidable (∀ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro h (fun h' i _ => h' i)

def Decidable.Nat.decidableFromBallLE' (h : { n : Nat // (∀ i, i ≤ n → p i) → ∀ i, p i }) :
  Decidable (∀ i, p i) := Decidable.Nat.decidableFromBallLE h.val h.property

def Decidable.Nat.decidableFromExistsLT (n : Nat)
  (h : (∃ i, p i) → (∃ i, i < n ∧ p i)) :
  Decidable (∃ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro (fun ⟨i, _, h'⟩ => ⟨i, h'⟩) h

def Decidable.Nat.decidableFromExistsLT' (h : { n : Nat // (∃ i, p i) → (∃ i, i < n ∧ p i) }) :
  Decidable (∃ i, p i) := Decidable.Nat.decidableFromExistsLT h.val h.property

def Decidable.Nat.decidableFromExistsLE (n : Nat)
  (h : (∃ i, p i) → (∃ i, i ≤ n ∧ p i)) :
  Decidable (∃ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro (fun ⟨i, _, h'⟩ => ⟨i, h'⟩) h

def Decidable.Nat.decidableFromExistsLE' (h : { n : Nat // (∃ i, p i) → (∃ i, i ≤ n ∧ p i) }) :
  Decidable (∃ i, p i) := Decidable.Nat.decidableFromExistsLE h.val h.property

end NatBounds

section IntBounds

variable {p : Int → Prop} [∀ i, Decidable (p i)]

def Decidable.Int.decidableFromBallLELE (lo hi : Int)
  (h : (∀ i, lo ≤ i → i ≤ hi → p i) → ∀ i, p i) :
  Decidable (∀ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro h (fun h' i _ _ => h' i)

def Decidable.Int.decidableFromBallLELE' (h : { lohi : Int × Int // (∀ i, lohi.1 ≤ i → i ≤ lohi.2 → p i) → ∀ i, p i }) :
  Decidable (∀ i, p i) := match h with
  | ⟨(lo, hi), h⟩ => Decidable.Int.decidableFromBallLELE lo hi h

-- this is missing from `Mathlib.Data.Int.Range`
instance Int.decidableExistsLELE (p : Int → Prop) [∀ i, Decidable (p i)] (m n : Int) :
    Decidable (∃ r, m ≤ r ∧ r ≤ n ∧ p r) :=
  decidable_of_iff (∃ r ∈ Int.range m (n + 1), p r :) <| by
    simp only [Int.mem_range_iff, and_assoc, Int.lt_add_one_iff]

def Decidable.Int.decidableFromExistsLELE' (lo hi : Int)
  (h : (∃ i, p i) → (∃ i, lo ≤ i ∧ i ≤ hi ∧ p i)) :
  Decidable (∃ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro (fun ⟨i, _, _, h'⟩ => ⟨i, h'⟩) h

end IntBounds

/-!
According to Lean reference manual, tactics in `autoParam` will
_not_ be invoked during instance synthesis. So we have to design
tactics for discharging the side goals required by the heuristics.
-/

section TCSynthAuxTactic

/-!
There are two ways to implement this "customized instance synthesis":
one is top-down, by matching on the expression and attempting to
provide the corresponding instance; the other is bottom-up, by
first finding out which _auxiliary instances_ might be useful in the overall
synthesis, trying to provide those instances, and then completing the
synthesis in one go at the top level.

The former seems to require more work so we go with the latter.
-/

/-- Traverse `e` in a way like `Meta.transform`, with these differences:
- `step` takes an array of free variables, which represents the free
  variables introduced along the way by `forallE` and `lam`.
- `step` returns `Unit`.
- There is only `post` step.
- `forallE` and `lam` are not be handled in a cascading way. -/
private partial def simpleBottomUpTraverse {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
  (e : Expr) (step : Array Expr → Expr → m Unit)
  (skipConstInApp := false)
  : m Unit := go #[] e
where go (fvars : Array Expr) (e : Expr) : m Unit := do
  let goWhole? ← do
    match e with
    | .forallE nm d b bi  => do
      go fvars d
      withLocalDecl nm bi d fun x => do
        let fvars' := fvars.push x
        go fvars' (b.instantiate1 x)
      pure true
    | .lam nm d b bi      => do
      withLocalDecl nm bi d fun x => do
        go fvars d
        let fvars' := fvars.push x
        go fvars' (b.instantiate1 x)
      pure true
    | .app ..             =>
      e.withApp fun f args => do
        unless skipConstInApp && f.isConst do go fvars f
        for arg in args do go fvars arg
      pure true
    | .mdata _ b          => go fvars b ; pure false
    | _                   => pure false
  if goWhole? then step fvars e

private inductive TCSynthAuxTacticResult where
  | notApplicable (ex : MessageData)
  | notTarget
  | doneWithoutAux
  | doneWithAux (inst : Expr)
  | auxFailed (ex : MessageData)
deriving Inhabited

instance : ToMessageData TCSynthAuxTacticResult where
  toMessageData
    | .notApplicable ex => m!"not applicable:\n{ex}"
    | .notTarget        => "not target"
    | .doneWithoutAux   => "done without aux"
    | .doneWithAux inst => m!"done with aux:\n{inst}"
    | .auxFailed ex     => m!"aux failed:\n{ex}"

abbrev TCSynthAuxTacticM := StateT (Array Expr) TacticM

/-- Try synthesizing `target` without any auxiliary instances. -/
private def trySynthWithoutAux (target : Expr) : MetaM Bool := do
  try
    let _ ← synthInstance target
    return true
  catch _ =>
    return false

/-!
Auxiliary instances may depend on each other. Considering this, there
are two ways to implement the following algorithm.
- Keep the invariant that all auxiliary instances are closed wrt. the
  local context of the main goal. Each time we find a new auxiliary
  instance, we immediately add it to the main goal's local context.
  A new auxiliary instance will be always synthesized under the local
  context of the main goal, so it can refer to all previously synthesized
  auxiliary instances.
- Still keep the invariant, but each time we want to synthesize a new
  auxiliary instance, we first add all previously synthesized auxiliary
  instances to the local context, then do the synthesis.

We go with the latter since the former requires inserting the free
variables introduced along the way of traverse into the local context
of the main goal, which is a bit annoying.
-/

/-- Try synthesizing `target` using the local instances `insts` and
a quasi-instance constructed by `qinst`. `qinst` is expected to be
evaluated _under a different local context_ which `insts` are
inserted to as local declarations, while this whole function
_does not do that_. -/
private def trySynthByAux (fvars insts : Array Expr) (target : Expr)
  (qinst : MetaM Expr)
  (subtypeGoalTactic : TSyntax `tactic) : TacticM (Sum Expr MessageData) := do
  -- create a fresh goal with type `target` and supply `insts` as local instances;
  -- `fvars'` are the free variables corresponding to `insts` in the new goal,
  -- we need to substitute them with their values for the eventually obtained synthesized `target`
  let (fvars', g) ← do
    let goriginal ← mkFreshExprMVar target
    let mut gres := goriginal.mvarId!
    let mut fvars' := #[]
    for inst in insts do
      let (fv, g') ← gres.let (← mkFreshUserName `inst) inst
      -- fvars' := fvars'.push (Expr.fvar fv)
      fvars' := fvars'.push fv
      gres := g'
    pure (fvars', gres)
  try
    let qinst ← g.withContext qinst
    -- NOTE: We allow synthesis failures here since some goals like
    -- `∀ ..., Decidable ...` might fail to be synthesized, even though
    -- its body can be synthesized. For that case, we handle it through
    -- manual `intros` and then `infer_instance`.
    let res ← g.apply (cfg := { allowSynthFailures := true }) qinst
    -- for now, only consider the cases where we get one or two goals
    -- `gdecpred?` is potentially the goal of shape `∀ ..., Decidable ...`,
    -- `g'` is the `Subtype` goal
    let (gdecpred?, g') ← match res with
      | [g1, g2]  =>
        let tmp ← g1.getType''
        if tmp.getAppFn'.isConstOf ``Subtype then pure (some g2, g1) else pure (some g1, g2)
      | [g']      => pure (none, g')
      | _         => throwError "applying {qinst} to {target} failed; expected 1 or 2 goals, got {res}"
    if let some gdecpred := gdecpred? then
      let goals ← evalTacticAt (← `(tactic| intros ; infer_instance )) gdecpred
      unless goals.isEmpty do throwError "failed to synthesize {gdecpred} by `intros ; infer_instance`"
    let goals ← evalTacticAt subtypeGoalTactic g'
    unless goals.isEmpty && (← g'.isAssigned) do throwError "failed to synthesize {g'} by `prove_subtype_by_guessing`"
    -- now, might confirm that `g` is proved
    let inst ← instantiateMVars (Expr.mvar g)
    if inst.hasMVar then throwError "synthesized auxiliary instance {g} has metavariables"
    -- close the auxiliary instance wrt. `fvars`
    let inst ← mkLambdaFVars fvars inst (usedOnly := true)
    let inst ← g.withContext do zetaDeltaFVars inst fvars'
    return .inl inst
  catch ex =>
    return .inr ex.toMessageData

private def auxSynthesizeCore (fvars : Array Expr) (e : Expr)
  (choices : List (MetaM Expr × TSyntax `tactic)) : TCSynthAuxTacticM TCSynthAuxTacticResult := do
  let mut results : Array TCSynthAuxTacticResult := #[]
  for (qinst, tac) in choices do
    let r ← go qinst tac
    if let .doneWithAux _ := r then
      return r
    results := results.push r
  return results[0]!
where go (qinst : MetaM Expr) (tac : TSyntax `tactic) : TCSynthAuxTacticM TCSynthAuxTacticResult := do
  let dec ← mkAppM ``Decidable #[e]
  if ← trySynthWithoutAux dec then return .doneWithoutAux
  let insts : Array Expr ← get
  let res ← trySynthByAux fvars insts dec qinst tac
  match res with
  | .inl inst =>
    modify (fun (s : Array Expr) => s.push inst)
    return .doneWithAux inst
  | .inr ex   => return .auxFailed ex

/-- Perform auxiliary instance synthesis for a proposition `e`
of the form `∀ i, p i`. -/
private def auxSynthesizeForall (fvars : Array Expr) (e : Expr) : TCSynthAuxTacticM TCSynthAuxTacticResult := do
  let Expr.forallE nm d b bi := e | return .notApplicable m!"not a ∀"
  let p := Expr.lam nm d b bi
  -- for now, only try among some predefined types and their quasi-instances;
  -- multiple quasi-instances may be applicable, so we return a list,
  -- in order of preference
  let generalSolver ← `(tactic| prove_subtype_by_guessing_simple_solver )
  let handlers : List (Expr × List (MetaM Expr × TSyntax `tactic)) :=
    [ (mkConst ``Nat,
        [(mkAppOptM ``Decidable.Nat.decidableFromBallLT' #[.some p],
          ← `(tactic| prove_subtype_by_guessing_nat_lt $generalSolver )),
         (mkAppOptM ``Decidable.Nat.decidableFromBallLE' #[.some p],
          ← `(tactic| prove_subtype_by_guessing_nat_le $generalSolver ))]),
      (mkConst ``Int,
        [(mkAppOptM ``Decidable.Int.decidableFromBallLELE' #[.some p],
          ← `(tactic| prove_subtype_by_guessing_int_lele $generalSolver ))]) ]
  let some (_, choices) ← handlers.findM? fun a => isDefEq d a.1
    | return .notTarget
  auxSynthesizeCore fvars e choices

/-- Perform auxiliary instance synthesis for a proposition `e`
of the form `∃ i, p i`. -/
private def auxSynthesizeExists (fvars : Array Expr) (e : Expr) : TCSynthAuxTacticM TCSynthAuxTacticResult := do
  let e := e.consumeMData
  let_expr Exists d p := e | return .notApplicable m!"not an ∃"
  let generalSolver ← `(tactic| prove_subtype_by_guessing_simple_solver )
  let handlers : List (Expr × List (MetaM Expr × TSyntax `tactic)) :=
    [ (mkConst ``Nat,
        [(mkAppOptM ``Decidable.Nat.decidableFromExistsLT' #[.some p],
          ← `(tactic| prove_subtype_by_guessing_nat_lt $generalSolver )),
         (mkAppOptM ``Decidable.Nat.decidableFromExistsLE' #[.some p],
          ← `(tactic| prove_subtype_by_guessing_nat_le $generalSolver ))]),
      (mkConst ``Int,
        [(mkAppOptM ``Decidable.Int.decidableFromExistsLELE' #[.some p],
          ← `(tactic| prove_subtype_by_guessing_int_lele $generalSolver ))]) ]
  let some (_, choices) ← handlers.findM? fun a => isDefEq d a.1
    | return .notTarget
  auxSynthesizeCore fvars e choices

/-- Synthesize auxiliary `Decidable` instances by traversing `e`
in a bottom-up manner. -/
partial def auxSynth (e : Expr) : TacticM Unit := do
  let mnd := simpleBottomUpTraverse (m := StateT (Array Expr) TacticM) e
    (skipConstInApp := true)
    fun fvars e => do
      unless ← Meta.isProp e do return
      let r ← auxSynthesizeForall fvars e
      trace[Loom.debug] m!"[auxSynthesizeForall] result for {e}: {r}"
      let r ← auxSynthesizeExists fvars e
      trace[Loom.debug] m!"[auxSynthesizeExists] result for {e}: {r}"
  let (_, insts) ← mnd.run #[]
  for inst in insts do
    let mv ← popMainGoal
    let (_, mv') ← mv.let (← mkFreshUserName `inst) inst
    pushGoal mv'

elab "infer_aux_decidable_instance" : tactic => do
  withMainContext do
    evalTactic (← `(tactic| dsimp -$(mkIdent `failIfUnchanged) only [$(mkIdent `loomAbstractionSimp):ident] ))
  let tgt ← getMainTarget
  auxSynth tgt

end TCSynthAuxTactic

end GuessingBounds

end DecidableHeuristics

end Loom.Testing
