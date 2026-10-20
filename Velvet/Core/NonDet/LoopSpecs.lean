module

public import Velvet.Core.NonDet.WP
public import Velvet.Core.Loop.Specs

/-!
# Loop specifications over `NonDetT`

The specifications `velvet_vcgen` applies to Velvet's `while` gadgets in `NonDetT`. A `NonDetT`
loop is a `repeatCont` node, whose WP allows either an invariant (partial correctness) or a
decreasing measure (total correctness), so the two core rules here unfold `NonDetT.wp` instead of
using `Loop.forInLoop_partial` and `Loop.forInLoop_total`. The specs above them are written as in
`Loop/Specs.lean`, which describes their conventions. `for` loops need no specs of their own: the
ones in `Loop/Specs.lean` apply to any monad with a WP.
-/

open Std.WP Lean.Order Loop Loop.Gadget WPPartial

universe u v w z

@[expose] public section

namespace NonDetT

/-- Partial-correctness rule for a `while` loop over `NonDetT`: every exit establishes `done`. -/
public theorem whileLoopPartial_nondet
    {mode : NondetMode} {m : Type u → Type v} {Pred EPred : Type u}
    {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
    {β : Type u} {init : β} {done? : Option (β → Pred)}
    (inv : β → Pred) (done : β → Pred)
    {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b)
        (fun r => match r with
          | .yield b' => inv b'
          | .done b' => done b') einv) :
    Triple (Gadget.whileLoopPartial init f inv done?) (inv init)
      (fun b => binderNameHint b done <| done b) einv := by
  apply Triple.intro
  dsimp only [whileLoopPartial, forIn, instForInLoopNonDetT, NonDetT.wp,
    binderNameHint]
  let stepPost : β → ForInStep β → Pred := fun _ r => match r with
    | .yield b' => inv b'
    | .done b' => done b'
  apply PartialOrder.rel_trans ?_ (left_le_join _ _)
  apply PartialOrder.rel_trans ?_
    (le_iSup (fun inv' => ⨆ (stepPost' : β → ForInStep β → Pred), _) inv)
  apply PartialOrder.rel_trans ?_ (le_iSup (fun stepPost' => _) stepPost)
  have hbody : ∀ b, inv b ⊑ (f () b).wp (stepPost b) einv :=
    fun b => (step b).le_wp
  have hyield : ∀ b b', stepPost b (.yield b') ⊑ inv b' := by
    intro b b'; exact PartialOrder.rel_refl
  have hdone : ∀ b b', stepPost b (.done b') ⊑
      (pure b' : NonDetT mode m β).wp (fun b => done b) einv := by
    intro b b'; exact PartialOrder.rel_refl
  have eqBody : (⌜∀ b, inv b ⊑ (f () b).wp (stepPost b) einv⌝ : Pred) = ⊤ := by
    simp [hbody]
  have eqYield : (⌜∀ b b', stepPost b (.yield b') ⊑ inv b'⌝ : Pred) = ⊤ := by
    simp [hyield]
  have eqDone : (⌜∀ b b', stepPost b (.done b') ⊑
      (pure b' : NonDetT mode m β).wp (fun b => done b) einv⌝ : Pred) = ⊤ := by
    simp [hdone]
  have eqDiv : (⌜∀ b, inv b ⊑ div_pre einv⌝ : Pred) = ⊤ := by
    simp [hdiv]
  rw [eqBody, eqYield, eqDone, eqDiv]
  exact le_meet _ _ _
    (le_meet _ _ _
      (le_meet _ _ _
        (le_meet _ _ _ (le_top _) PartialOrder.rel_refl)
        (le_top _))
      (le_top _))
    (le_top _)

/-- Total-correctness rule for a `while` loop over `NonDetT`: every exit establishes `done`. -/
public theorem whileLoopTotal_nondet
    {mode : NondetMode} {m : Type u → Type v} {Pred EPred : Type u}
    {div_post : EPred} {div_pre : EPred → Pred}
    [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
    {β : Type u} {init : β} {done? : Option (β → Pred)}
    (inv : β → Pred) (done : β → Pred) (measure : β → Named.Measure)
    {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    (step : ∀ b,
      Triple (f () b)
        (binderNameHint b inv <| inv b)
        (fun r => match r with
          | .yield b' =>
              match measure b, measure b' with
              | ⟨name, stx, current⟩, ⟨_, _, next⟩ =>
                  ⌜Named.mk name stx (next < current)⌝ ⊓ inv b'
          | .done b' => done b')
        einv) :
    Triple (Gadget.whileLoopTotal init f inv done? measure) (inv init)
      (fun b => binderNameHint b done <| done b) einv := by
  apply Triple.intro
  dsimp only [whileLoopTotal, forIn, instForInLoopNonDetT, NonDetT.wp,
    binderNameHint]
  let inv' : ForInStep β → Pred := fun
    | .yield b => inv b
    | .done b => done b
  let measure' : β → Nat := fun b => (measure b).value
  apply PartialOrder.rel_trans ?_ (right_le_join _ _)
  apply PartialOrder.rel_trans ?_
    (le_iSup (fun inv' => ⨆ (measure' : β → Nat), _) inv')
  apply PartialOrder.rel_trans ?_ (le_iSup (fun measure' => _) measure')
  have hbody : ∀ b, inv' (.yield b) ⊑ (f () b).wp
      (fun r => match r with
        | .yield b' => inv' (.yield b') ⊓ ⌜measure' b' < measure' b⌝
        | .done b' => inv' (.done b')) einv := by
    intro b
    apply PartialOrder.rel_trans (step b).le_wp
    apply WP.wp_consequence
    intro r
    cases r with
    | done b' => exact PartialOrder.rel_refl
    | yield b' =>
      dsimp [inv', measure']
      cases hb : measure b with
      | mk name stx current =>
        cases hb' : measure b' with
        | mk name' stx' next =>
          simp only [Named.mk_eq]
          exact le_meet _ _ _ (meet_le_right _ _) (meet_le_left _ _)
  have hdone : ∀ b, inv' (.done b) ⊑
      (Pure.pure (f := NonDetT mode m) b).wp (fun b => done b) einv := by
    intro b
    exact PartialOrder.rel_refl
  have eqBody : (⌜∀ b, inv' (.yield b) ⊑ (f () b).wp
      (fun r => match r with
        | .yield b' => inv' (.yield b') ⊓ ⌜measure' b' < measure' b⌝
        | .done b' => inv' (.done b')) einv⌝ : Pred) = ⊤ := by
    simp [hbody]
  have eqDone : (⌜∀ b, inv' (.done b) ⊑
      (Pure.pure (f := NonDetT mode m) b).wp (fun b => done b) einv⌝ : Pred) = ⊤ := by
    simp [hdone]
  erw [eqBody, eqDone]
  exact le_meet _ _ _
    (le_meet _ _ _ (le_top _) PartialOrder.rel_refl)
    (le_top _)

section Specs
variable {m : Type u → Type v} {Pred EPred : Type u} {div_post : EPred} {div_pre : EPred → Pred}
  [Monad m] [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
  [Assertion EPred] [WPMonad m Pred EPred]
  [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]

/-- The spec for `Gadget.whileLoopPartial` without `done_with`: every exit goes straight to the code
after the loop. -/
@[spec 1250]
public theorem Spec.whileLoopPartial
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    {Q : β → Pred} (inv : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b) (binderNameHint b inv <| inv b) (stepPost inv Q) einv) :
    Triple (Gadget.whileLoopPartial init f inv none) (inv init) Q einv :=
  whileLoopPartial_nondet inv Q hdiv fun b =>
    triple_post_le (step b) fun r => by cases r <;> exact PartialOrder.rel_refl

/-- The spec for `Gadget.whileLoopPartial` with `done_with`: every exit establishes `done`, which the
code after the loop starts from. -/
@[spec 1250]
public theorem Spec.whileLoopPartialAndDone
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    (inv done : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple (f () b) (binderNameHint b inv <| inv b) (stepPost inv done) einv) :
    Triple (Gadget.whileLoopPartial init f inv (some done)) (inv init)
      (fun b => binderNameHint b done <| done b) einv :=
  whileLoopPartial_nondet inv done hdiv fun b =>
    triple_post_le (step b) fun r => by cases r <;> exact PartialOrder.rel_refl

/-- The spec for `Gadget.whileLoopPartialReturning` with `done_with`: a `return` goes straight to the
code after the loop, and every other exit establishes `done`. -/
@[spec 1250]
public theorem Spec.whileLoopPartialAndDoneReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv done : τ → Pred)
    (hdiv : ∀ s, inv s ⊑ div_pre einv)
    (step : ∀ s, Triple (f () (none, s)) (binderNameHint s inv <| inv s)
      (stepPost (noReturn inv) (onExit Q done)) einv)
    (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple (Gadget.whileLoopPartialReturning init f inv (some done)) (noReturn inv init) Q einv :=
  triple_onExit (whileLoopPartial_nondet (done? := none) (noReturn inv) (onExit Q done) (noReturn_le hdiv) fun b =>
    triple_post_le (noReturn_step (inv := inv) (x := f ())
      (post := fun _ => stepPost (noReturn inv) (onExit Q done)) step b)
      fun r => by cases r <;> exact PartialOrder.rel_refl) hD

/-- The spec for `Gadget.whileLoopPartialReturning` without `done_with`: every exit goes straight to
the code after the loop. -/
@[spec 1250]
public theorem Spec.whileLoopPartialReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv : τ → Pred)
    (hdiv : ∀ s, inv s ⊑ div_pre einv)
    (step : ∀ s, Triple (f () (none, s)) (binderNameHint s inv <| inv s)
      (stepPost (noReturn inv) Q) einv) :
    Triple (Gadget.whileLoopPartialReturning init f inv none) (noReturn inv init) Q einv :=
  whileLoopPartial_nondet (done? := none) (noReturn inv) Q (noReturn_le hdiv) fun b =>
    triple_post_le (noReturn_step (inv := inv) (x := f ())
      (post := fun _ => stepPost (noReturn inv) Q) step b)
      fun r => by cases r <;> exact PartialOrder.rel_refl

/-- The spec for `Gadget.whileLoopTotal` without `done_with`: every exit goes straight to the code
after the loop. -/
@[spec 1250]
public theorem Spec.whileLoopTotal
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    {Q : β → Pred} (inv : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure Q b) einv) :
    Triple (Gadget.whileLoopTotal init f inv none measure) (inv init) Q einv :=
  whileLoopTotal_nondet inv Q measure fun b =>
    triple_post_le (step b) fun r => by cases r <;> exact PartialOrder.rel_refl

/-- The spec for `Gadget.whileLoopTotal` with `done_with`: every exit establishes `done`, which the
code after the loop starts from. -/
@[spec 1250]
public theorem Spec.whileLoopTotalAndDone
    {β : Type u} {init : β} {f : Unit → β → NonDetT mode m (ForInStep β)} {einv : EPred}
    (inv done : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure done b) einv) :
    Triple (Gadget.whileLoopTotal init f inv (some done) measure) (inv init)
      (fun b => binderNameHint b done <| done b) einv :=
  whileLoopTotal_nondet inv done measure fun b =>
    triple_post_le (step b) fun r => by cases r <;> exact PartialOrder.rel_refl

/-- The spec for `Gadget.whileLoopTotalReturning` with `done_with`: a `return` goes straight to the
code after the loop, and every other exit establishes `done`. -/
@[spec 1250]
public theorem Spec.whileLoopTotalAndDoneReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv done : τ → Pred) (measure : τ → Named.Measure)
    (step : ∀ s,
      Triple (f () (none, s)) (binderNameHint s inv <| inv s)
        (stepPostDecreasing (noReturn inv) (fun b => measure b.2) (onExit Q done) (none, s)) einv)
    (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple (Gadget.whileLoopTotalReturning init f inv (some done) measure) (noReturn inv init) Q einv :=
  triple_onExit (whileLoopTotal_nondet (done? := none) (noReturn inv) (onExit Q done) (fun b => measure b.2) fun b =>
    triple_post_le (noReturn_step (inv := inv) (x := f ())
      (post := fun b => stepPostDecreasing (noReturn inv) (fun b => measure b.2) (onExit Q done) b) step b)
      fun r => by cases r <;> exact PartialOrder.rel_refl) hD

/-- The spec for `Gadget.whileLoopTotalReturning` without `done_with`: every exit goes straight to
the code after the loop. -/
@[spec 1250]
public theorem Spec.whileLoopTotalReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → NonDetT mode m (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv : τ → Pred) (measure : τ → Named.Measure)
    (step : ∀ s,
      Triple (f () (none, s)) (binderNameHint s inv <| inv s)
        (stepPostDecreasing (noReturn inv) (fun b => measure b.2) Q (none, s)) einv) :
    Triple (Gadget.whileLoopTotalReturning init f inv none measure) (noReturn inv init) Q einv :=
  whileLoopTotal_nondet (done? := none) (noReturn inv) Q (fun b => measure b.2) fun b =>
    triple_post_le (noReturn_step (inv := inv) (x := f ())
      (post := fun b => stepPostDecreasing (noReturn inv) (fun b => measure b.2) Q b) step b)
      fun r => by cases r <;> exact PartialOrder.rel_refl

end Specs

end NonDetT

end
