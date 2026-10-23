module

public import Velvet.Core.FreerMonad.WP
public import Velvet.Core.Loop.Specs

/-!
# Loop specifications for `FreerMonad`

The `while` specs of `Velvet.Core.Loop.Specs`, for a `FreerMonad e` interpreted into `m`. Loops
route to `iter`, so each spec is a wrapper around one of two core lemmas about `iter`.
-/

@[expose] public section

open Std.WP Lean.Order WPPartial Loop Loop.Gadget

universe u v z

namespace FreerMonad

variable {m : Type u → Type v} {Pred EPred : Type u} {div_post : EPred} {div_pre : EPred → Pred}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
  [∀ γ, CCPO (m γ)] [WPPartial m Pred EPred div_post div_pre]
  {e : Type u → Type z} [∀ α, WP (e α) α Pred EPred]

/-- Partial-correctness rule for `iter`: every iteration re-establishes `inv`, and every exit
establishes `exit`. -/
theorem whileLoopPartial_core
    {β : Type u} {init : β} {f : Unit → β → FreerMonad e (ForInStep β)} {einv : EPred}
    (inv exit : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple m (f () b) (binderNameHint b inv <| inv b) (stepPost inv exit) einv) :
    Triple m (forIn PartialLoop.mk init f) (inv init) exit einv := by
  letI := wpMonadInst (m := m) (e := e) (div_post := div_post) (div_pre := div_pre)
  refine ⟨?_⟩
  change inv init ⊑ FreerMonad.wp (m := m) (.iter init (f ()) .ret) exit einv
  simp only [FreerMonad.wp]
  apply le_join_of_le_left
  apply le_iSup_of_le inv
  apply le_iSup_of_le (fun _ => stepPost inv exit)
  refine le_meet _ _ _ (le_meet _ _ _ (le_meet _ _ _ (le_meet _ _ _ ?_ PartialOrder.rel_refl) ?_) ?_) ?_
  · exact le_ofProp _ _ fun b => (step b).le_wp
  · exact le_ofProp _ _ fun _ _ => PartialOrder.rel_refl
  · exact le_ofProp _ _ fun _ _ => PartialOrder.rel_refl
  · exact le_ofProp _ _ hdiv

/-- Total-correctness rule for `iter`: every iteration re-establishes `inv` and decreases
`measure`, and every exit establishes `exit`. -/
theorem whileLoopTotal_core
    {β : Type u} {init : β} {f : Unit → β → FreerMonad e (ForInStep β)} {einv : EPred}
    (inv exit : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple m (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure exit b) einv) :
    Triple m (forIn Lean.Loop.mk init f) (inv init) exit einv := by
  letI := wpMonadInst (m := m) (e := e) (div_post := div_post) (div_pre := div_pre)
  refine ⟨?_⟩
  change inv init ⊑ FreerMonad.wp (m := m) (.iter init (f ()) .ret) exit einv
  simp only [FreerMonad.wp]
  apply le_join_of_le_right
  apply le_iSup_of_le (fun | .yield b => inv b | .done b => exit b)
  apply le_iSup_of_le (fun b => (measure b).value)
  refine le_meet _ _ _ (le_meet _ _ _ ?_ PartialOrder.rel_refl)
    (le_ofProp _ _ fun _ => PartialOrder.rel_refl)
  refine le_ofProp _ _ fun b => PartialOrder.rel_trans (step b).le_wp ?_
  apply WP.wp_consequence
  intro r
  cases r with
  | done b' => exact PartialOrder.rel_refl
  | yield b' =>
    show stepPostDecreasing inv measure exit b (.yield b') ⊑ _
    cases hb : measure b with
    | mk name stx current =>
      cases hb' : measure b' with
      | mk name' stx' next =>
        simp only [stepPostDecreasing, stepPost, hb, hb', Named.mk_eq]
        exact le_meet _ _ _ (meet_le_right _ _) (meet_le_left _ _)

/-- A partial-correctness `while` loop without `done_with`. -/
theorem Spec.whileLoopPartial
    {β : Type u} {init : β} {f : Unit → β → FreerMonad e (ForInStep β)} {einv : EPred}
    {Q : β → Pred} (inv : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple m (f () b) (binderNameHint b inv <| inv b) (stepPost inv Q) einv) :
    Triple m (Gadget.whileLoopPartial init f inv none) (inv init) Q einv :=
  whileLoopPartial_core inv Q hdiv step

/-- A partial-correctness `while` loop with `done_with`. -/
theorem Spec.whileLoopPartialAndDone
    {β : Type u} {init : β} {f : Unit → β → FreerMonad e (ForInStep β)} {einv : EPred}
    (inv done : β → Pred)
    (hdiv : ∀ b, inv b ⊑ div_pre einv)
    (step : ∀ b, Triple m (f () b) (binderNameHint b inv <| inv b) (stepPost inv done) einv) :
    Triple m (Gadget.whileLoopPartial init f inv (some done)) (inv init)
      (fun b => binderNameHint b done <| done b) einv :=
  whileLoopPartial_core inv done hdiv step

/-- A partial-correctness `while` loop with `done_with` whose body can `return`. -/
theorem Spec.whileLoopPartialAndDoneReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → FreerMonad e (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv done : τ → Pred)
    (hdiv : ∀ s, inv s ⊑ div_pre einv)
    (step : ∀ s, Triple m (f () (none, s)) (binderNameHint s inv <| inv s)
      (stepPost (noReturn inv) (onExit Q done)) einv)
    (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple m (Gadget.whileLoopPartialReturning init f inv (some done)) (noReturn inv init) Q einv :=
  letI := wpMonadInst (m := m) (e := e) (div_post := div_post) (div_pre := div_pre)
  triple_onExit (whileLoopPartial_core (noReturn inv) _ (noReturn_le hdiv)
    (noReturn_step (inv := inv) (x := f ()) (post := fun _ => stepPost (noReturn inv) (onExit Q done))
      step)) hD

/-- A partial-correctness `while` loop without `done_with` whose body can `return`. -/
theorem Spec.whileLoopPartialReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → FreerMonad e (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv : τ → Pred)
    (hdiv : ∀ s, inv s ⊑ div_pre einv)
    (step : ∀ s, Triple m (f () (none, s)) (binderNameHint s inv <| inv s)
      (stepPost (noReturn inv) Q) einv) :
    Triple m (Gadget.whileLoopPartialReturning init f inv none) (noReturn inv init) Q einv :=
  letI := wpMonadInst (m := m) (e := e) (div_post := div_post) (div_pre := div_pre)
  whileLoopPartial_core (noReturn inv) Q (noReturn_le hdiv)
    (noReturn_step (inv := inv) (x := f ()) (post := fun _ => stepPost (noReturn inv) Q) step)

/-- A total-correctness `while` loop without `done_with`. -/
theorem Spec.whileLoopTotal
    {β : Type u} {init : β} {f : Unit → β → FreerMonad e (ForInStep β)} {einv : EPred}
    {Q : β → Pred} (inv : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple m (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure Q b) einv) :
    Triple m (Gadget.whileLoopTotal init f inv none measure) (inv init) Q einv :=
  whileLoopTotal_core inv Q measure step

/-- A total-correctness `while` loop with `done_with`. -/
theorem Spec.whileLoopTotalAndDone
    {β : Type u} {init : β} {f : Unit → β → FreerMonad e (ForInStep β)} {einv : EPred}
    (inv done : β → Pred) (measure : β → Named.Measure)
    (step : ∀ b,
      Triple m (f () b) (binderNameHint b inv <| inv b) (stepPostDecreasing inv measure done b) einv) :
    Triple m (Gadget.whileLoopTotal init f inv (some done) measure) (inv init)
      (fun b => binderNameHint b done <| done b) einv :=
  whileLoopTotal_core inv done measure step

/-- A total-correctness `while` loop with `done_with` whose body can `return`. -/
theorem Spec.whileLoopTotalAndDoneReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → FreerMonad e (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv done : τ → Pred) (measure : τ → Named.Measure)
    (step : ∀ s,
      Triple m (f () (none, s)) (binderNameHint s inv <| inv s)
        (stepPostDecreasing (noReturn inv) (fun b => measure b.2) (onExit Q done) (none, s)) einv)
    (hD : ∀ s, binderNameHint s done (done s) ⊑ Q (none, s)) :
    Triple m (Gadget.whileLoopTotalReturning init f inv (some done) measure) (noReturn inv init) Q einv :=
  letI := wpMonadInst (m := m) (e := e) (div_post := div_post) (div_pre := div_pre)
  triple_onExit (whileLoopTotal_core (noReturn inv) _ (fun b => measure b.2)
    (noReturn_step (inv := inv) (x := f ())
      (post := fun b => stepPostDecreasing (noReturn inv) (fun b => measure b.2) (onExit Q done) b)
      step)) hD

/-- A total-correctness `while` loop without `done_with` whose body can `return`. -/
theorem Spec.whileLoopTotalReturning
    {γ τ : Type u} {init : Option γ × τ}
    {f : Unit → Option γ × τ → FreerMonad e (ForInStep (Option γ × τ))} {einv : EPred}
    {Q : Option γ × τ → Pred} (inv : τ → Pred) (measure : τ → Named.Measure)
    (step : ∀ s,
      Triple m (f () (none, s)) (binderNameHint s inv <| inv s)
        (stepPostDecreasing (noReturn inv) (fun b => measure b.2) Q (none, s)) einv) :
    Triple m (Gadget.whileLoopTotalReturning init f inv none measure) (noReturn inv init) Q einv :=
  letI := wpMonadInst (m := m) (e := e) (div_post := div_post) (div_pre := div_pre)
  whileLoopTotal_core (noReturn inv) Q (fun b => measure b.2)
    (noReturn_step (inv := inv) (x := f ())
      (post := fun b => stepPostDecreasing (noReturn inv) (fun b => measure b.2) Q b) step)

end FreerMonad

end
