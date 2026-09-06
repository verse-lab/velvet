module

prelude
public import Lean
public meta import Lean.Meta.Tactic.Grind.Types
public import Init.Data.Nat.Basic
public import Init.Data.Int.Basic

open Lean Meta Elab Tactic

initialize
  registerTraceClass `Velvet.testing

namespace Velvet.Testing

section DecidableHeuristics

section GuessingBounds

/-- Gather all grounded (i.e., without loose bvars and mvars)
sub-expressions of type `ty` in `e`. A grounded expression can be
scored by `scoring` when it is an argument of an application.
`scoring` takes the function of the application and the argument index
and returns a score (the bigger the better). -/
public meta partial def gatherClosedSubExprs (ty e : Expr) (scoring : Expr → Nat → Nat) :
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
public meta partial def proveSubtypeByGuessing (splitProd? : Bool) (scoring : Array (Expr → Nat → Nat))
  (solver : TSyntax `tactic) : TacticM Unit := withMainContext do
  let ty ← getMainTarget
  let_expr Subtype α p := ty | throwError "the goal should be Subtype, got {ty}"
  let comps := List.toArray <| if splitProd? then splitProdType α else [α]
  let scoring :=
    if scoring.size ≥ comps.size then scoring
    else scoring ++ Array.replicate (comps.size - scoring.size) (fun _ _ => 0)
  let candidates ← comps.zipWithM (fun β sc => do
    let tmp ← gatherClosedSubExprs β p sc |>.run {}
    pure (β, tmp.2)) scoring
  let candidates ← mergeCandidates candidates
  let r ← tryEachCandidate α candidates solver
  unless r.isSome do
    throwError "failed to find a bound for {p}"
where
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
      let ty' ← instantiateMVars ty'
      let lvls := ty'.getAppFn.const?.elim [] Prod.snd
      let pairs := s'.toArray.flatMap fun (e1, score1) =>
        res.map fun (e2, score2) => (mkAppN (mkConst ``Prod.mk lvls) #[tyl, tyr, e1, e2], score1 + score2)
      pure (ty', pairs)
    let res := tmp.2.qsort fun (e1, sc1) (e2, sc2) =>
      (sc1 > sc2) || (sc1 == sc2 && e1.sizeWithoutSharing < e2.sizeWithoutSharing)
    pure <| res.toList.map Prod.fst
 tryEachCandidate (ty : Expr) (candidates : List Expr) (solver : TSyntax `tactic) : TacticM (Option Expr) := withMainContext do
  for c in candidates do
    let r ← try
      withoutRecover do
      evalTactic (← `(tactic| refine $(mkIdent ``Subtype.mk) ?_ ?_ ))
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
    | .inr _ => pure ()
  return Option.none

public meta def scoreLELTLHSRHS (lt? smaller? : Bool) (f : Expr) (i : Nat) : Nat :=
  if let some nm := f.consumeMData.constName? then
    if ((i == 2) || (i == 3)) &&
       (if lt? then (nm == ``LT.lt || nm == ``GT.gt) else (nm == ``LE.le || nm == ``GE.ge)) then
      let b0 := smaller? ^^ (i == 2)
      let b1 := (if lt? then (nm == ``LT.lt) else (nm == ``LE.le)) ^^ b0
      if b1 then 2 else 0
    else 0
  else 0

macro "prove_subtype_by_guessing_simple_solver" : tactic =>
  `(tactic| (intros ; solve | omega | grind | (simp at * ; grind)) )

syntax "prove_subtype_by_guessing_nat_lt" tactic : tactic
elab_rules : tactic
  | `(tactic| prove_subtype_by_guessing_nat_lt $solver:tactic) =>
    proveSubtypeByGuessing false #[scoreLELTLHSRHS true false] solver

syntax "prove_subtype_by_guessing_nat_le" tactic : tactic
elab_rules : tactic
  | `(tactic| prove_subtype_by_guessing_nat_le $solver:tactic) =>
    proveSubtypeByGuessing false #[scoreLELTLHSRHS false false] solver

syntax "prove_subtype_by_guessing_int_lele" tactic : tactic
elab_rules : tactic
  | `(tactic| prove_subtype_by_guessing_int_lele $solver:tactic) =>
    proveSubtypeByGuessing true #[scoreLELTLHSRHS false true, scoreLELTLHSRHS false false] solver

section NatBounds

variable {p : Nat → Prop} [∀ i, Decidable (p i)]

public def Decidable.Nat.decidableFromBallLT (n : Nat)
  (h : (∀ i, i < n → p i) → ∀ i, p i) :
  Decidable (∀ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro h (fun h' i _ => h' i)

public def Decidable.Nat.decidableFromBallLT' (h : { n : Nat // (∀ i, i < n → p i) → ∀ i, p i }) :
  Decidable (∀ i, p i) := Decidable.Nat.decidableFromBallLT h.val h.property

public def Decidable.Nat.decidableFromBallLE (n : Nat)
  (h : (∀ i, i ≤ n → p i) → ∀ i, p i) :
  Decidable (∀ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro h (fun h' i _ => h' i)

public def Decidable.Nat.decidableFromBallLE' (h : { n : Nat // (∀ i, i ≤ n → p i) → ∀ i, p i }) :
  Decidable (∀ i, p i) := Decidable.Nat.decidableFromBallLE h.val h.property

public def Decidable.Nat.decidableFromExistsLT (n : Nat)
  (h : (∃ i, p i) → (∃ i, i < n ∧ p i)) :
  Decidable (∃ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro (fun ⟨i, _, h'⟩ => ⟨i, h'⟩) h

public def Decidable.Nat.decidableFromExistsLT' (h : { n : Nat // (∃ i, p i) → (∃ i, i < n ∧ p i) }) :
  Decidable (∃ i, p i) := Decidable.Nat.decidableFromExistsLT h.val h.property

public def Decidable.Nat.decidableFromExistsLE (n : Nat)
  (h : (∃ i, p i) → (∃ i, i ≤ n ∧ p i)) :
  Decidable (∃ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro (fun ⟨i, _, h'⟩ => ⟨i, h'⟩) h

public def Decidable.Nat.decidableFromExistsLE' (h : { n : Nat // (∃ i, p i) → (∃ i, i ≤ n ∧ p i) }) :
  Decidable (∃ i, p i) := Decidable.Nat.decidableFromExistsLE h.val h.property

end NatBounds

section IntBounds

variable {p : Int → Prop} [∀ i, Decidable (p i)]

public def decidableForallIntLELE (p : Int → Prop) [∀ i, Decidable (p i)] (lo hi : Int) :
    Decidable (∀ r, lo ≤ r → r ≤ hi → p r) := by
  if hlo : lo ≤ hi then
    let bound := (hi - lo).toNat
    let p' (k : Nat) : Prop := p (lo + k)
    have : Decidable (∀ k, k ≤ bound → p' k) := by infer_instance
    if h : ∀ k, k ≤ bound → p' k then
      apply isTrue
      intro r hr_lo hr_hi
      have hk : (r - lo).toNat ≤ bound := by omega
      have hp := h (r - lo).toNat hk
      dsimp [p'] at hp
      have heq : lo + ((r - lo).toNat : Int) = r := by omega
      rwa [heq] at hp
    else
      apply isFalse
      intro hall
      apply h
      intro k hk
      dsimp [p']
      have hr_lo : lo ≤ lo + (k : Int) := by omega
      have hr_hi : lo + (k : Int) ≤ hi := by omega
      exact hall (lo + (k : Int)) hr_lo hr_hi
  else
    apply isTrue
    intro r hr_lo hr_hi
    omega

public def decidableExistsIntLELE (p : Int → Prop) [∀ i, Decidable (p i)] (lo hi : Int) :
    Decidable (∃ r, lo ≤ r ∧ r ≤ hi ∧ p r) := by
  if hlo : lo ≤ hi then
    let bound := (hi - lo).toNat
    let p' (k : Nat) : Prop := p (lo + k)
    have : Decidable (∃ k, k ≤ bound ∧ p' k) := Nat.decidableExistsLE (p := p') bound
    if h : ∃ k, k ≤ bound ∧ p' k then
      apply isTrue
      rcases h with ⟨k, hk_le, hk_p⟩
      refine ⟨lo + k, ?_, ?_, hk_p⟩
      · omega
      · omega
    else
      apply isFalse
      intro ⟨r, hr_lo, hr_hi, hr_p⟩
      apply h
      refine ⟨(r - lo).toNat, ?_, ?_⟩
      · omega
      · dsimp [p']
        have heq : lo + ((r - lo).toNat : Int) = r := by omega
        rw [heq]
        exact hr_p
  else
    apply isFalse
    intro ⟨r, hr_lo, hr_hi, _⟩
    omega

public instance (priority := default) (p : Int → Prop) [∀ i, Decidable (p i)] (lo hi : Int) :
    Decidable (∀ r, lo ≤ r → r ≤ hi → p r) :=
  decidableForallIntLELE p lo hi

public instance (priority := default) (p : Int → Prop) [∀ i, Decidable (p i)] (lo hi : Int) :
    Decidable (∃ r, lo ≤ r ∧ r ≤ hi ∧ p r) :=
  decidableExistsIntLELE p lo hi

public def Decidable.Int.decidableFromBallLELE (lo hi : Int)
  (h : (∀ i, lo ≤ i → i ≤ hi → p i) → ∀ i, p i) :
  Decidable (∀ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro h (fun h' i _ _ => h' i)

public def Decidable.Int.decidableFromBallLELE' (h : { lohi : Int × Int // (∀ i, lohi.1 ≤ i → i ≤ lohi.2 → p i) → ∀ i, p i }) :
  Decidable (∀ i, p i) := match h with
  | ⟨(lo, hi), h⟩ => Decidable.Int.decidableFromBallLELE lo hi h

public def Decidable.Int.decidableFromExistsLELE (lo hi : Int)
  (h : (∃ i, p i) → (∃ i, lo ≤ i ∧ i ≤ hi ∧ p i)) :
  Decidable (∃ i, p i) :=
  decidable_of_decidable_of_iff <| Iff.intro (fun ⟨i, _, _, h'⟩ => ⟨i, h'⟩) h

public def Decidable.Int.decidableFromExistsLELE' (h : { lohi : Int × Int // (∃ i, p i) → (∃ i, lohi.1 ≤ i ∧ i ≤ lohi.2 ∧ p i) }) :
  Decidable (∃ i, p i) := match h with
  | ⟨(lo, hi), h⟩ => Decidable.Int.decidableFromExistsLELE lo hi h

end IntBounds

section TCSynthAuxTactic

private meta partial def simpleBottomUpTraverse {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
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

private meta inductive TCSynthAuxTacticResult where
  | notApplicable (ex : MessageData)
  | notTarget
  | doneWithoutAux
  | doneWithAux (inst : Expr)
  | auxFailed (ex : MessageData)
deriving Inhabited

abbrev TCSynthAuxTacticM := StateT (Array Expr) TacticM

private meta def trySynthWithoutAux (target : Expr) : MetaM Bool := do
  try
    let _ ← synthInstance target
    return true
  catch _ =>
    return false

public meta def _root_.Lean.MVarId.letDecl (mvarId : MVarId) (name : Name) (val : Expr) (type? : Option Expr := none) : MetaM (FVarId × MVarId) := do
  let type ← match type? with
    | some ty => pure ty
    | none => inferType val
  let mvarId' ← mvarId.define name type val
  mvarId'.intro1P

private meta def trySynthByAux (fvars insts : Array Expr) (target : Expr)
  (qinst : MetaM Expr)
  (subtypeGoalTactic : TSyntax `tactic) : TacticM (Sum Expr MessageData) := do
  let (fvars', g) ← do
    let goriginal ← mkFreshExprMVar target
    let mut gres := goriginal.mvarId!
    let mut fvars' := #[]
    for inst in insts do
      let (fv, g') ← gres.letDecl (← mkFreshUserName `inst) inst
      fvars' := fvars'.push fv
      gres := g'
    pure (fvars', gres)
  try
    let qinst ← g.withContext qinst
    let res ← g.apply (cfg := { allowSynthFailures := true }) qinst
    let (gdecpred?, g') ← match res with
      | [g1, g2]  =>
        let tmp ← g1.getType'
        if tmp.getAppFn.isConstOf ``Subtype then pure (some g2, g1) else pure (some g1, g2)
      | [g']      => pure (none, g')
      | _         => throwError "applying {qinst} to {target} failed; expected 1 or 2 goals, got {res}"
    if let some gdecpred := gdecpred? then
      let goals ← evalTacticAt (← `(tactic| intros ; infer_instance )) gdecpred
      unless goals.isEmpty do throwError "failed to synthesize {gdecpred} by `intros ; infer_instance`"
    let goals ← evalTacticAt subtypeGoalTactic g'
    unless goals.isEmpty && (← g'.isAssigned) do throwError "failed to synthesize {g'} by `prove_subtype_by_guessing`"
    let inst ← instantiateMVars (Expr.mvar g)
    if inst.hasMVar then throwError "synthesized auxiliary instance {g} has metavariables"
    let inst ← mkLambdaFVars fvars inst (usedOnly := true)
    let inst ← g.withContext do zetaDeltaFVars inst fvars'
    return .inl inst
  catch ex =>
    return .inr ex.toMessageData

private meta def auxSynthesizeCore (fvars : Array Expr) (e : Expr)
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

private meta def auxSynthesizeForall (fvars : Array Expr) (e : Expr) : TCSynthAuxTacticM TCSynthAuxTacticResult := do
  let Expr.forallE nm d b bi := e | return .notApplicable m!"not a ∀"
  let p := Expr.lam nm d b bi
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

private meta def auxSynthesizeExists (fvars : Array Expr) (e : Expr) : TCSynthAuxTacticM TCSynthAuxTacticResult := do
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

public meta partial def auxSynth (e : Expr) : TacticM Unit := do
  let mnd := simpleBottomUpTraverse (m := StateT (Array Expr) TacticM) e
    (skipConstInApp := true)
    fun fvars e => do
      unless ← Meta.isProp e do return
      let _ ← auxSynthesizeForall fvars e
      let _ ← auxSynthesizeExists fvars e
  let (_, insts) ← mnd.run #[]
  for inst in insts do
    let mv ← getMainGoal
    let (_, mv') ← mv.letDecl (← mkFreshUserName `inst) inst
    replaceMainGoal [mv']

register_simp_attr velvetAbstractionSimp
register_simp_attr loomAbstractionSimp

syntax "infer_aux_decidable_instance" : tactic
elab_rules : tactic
  | `(tactic| infer_aux_decidable_instance) => do
    withMainContext do
      evalTactic (← `(tactic| try dsimp -failIfUnchanged only [$(mkIdent `velvetAbstractionSimp):ident, $(mkIdent `loomAbstractionSimp):ident] ))
    let tgt ← getMainTarget
    auxSynth tgt

end TCSynthAuxTactic

end GuessingBounds

end DecidableHeuristics

end Velvet.Testing
