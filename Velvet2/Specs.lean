import Velvet2.Named
import Std.Internal.Do

open Std.Internal.Do

variable {m : Type u → Type v} {Pred EPred : Type u}

/-- A runtime no-op that introduces an assertion into verification conditions. -/
def assertGadget [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] (_assertion : Pred) : m PUnit := pure ⟨⟩

namespace Velvet2.Spec

open Lean.Order

/-- Specification for `assertGadget`: the precondition requires both `assertion` and the
Heyting implication `assertion ⇨ post ⟨⟩`, so the assertion is available when proving the
continuation. -/
@[spec]
theorem assertGadgetSpec {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (assertion : Pred) [∀ a : Pred, PreservesSup (meet a)]
    {post : PUnit → Pred} {epost : EPred} :
    Triple (_root_.assertGadget (m := m) assertion)
      (assertion ⊓ (assertion ⇨ post ⟨⟩)) post epost := by
  simpa [_root_.assertGadget] using
    (Triple.pure (m := m)
      (pre := assertion ⊓ (assertion ⇨ post ⟨⟩))
      (post := post) (epost := epost) (a := ⟨⟩)
      (h := meet_himp_le))

/--
Metadata adapter for Lean's native annotated-repeat-loop gadget. `while'` passes its natural-number
measure as `Named.Measure` solely to retain the clause name and source location. This specification
strips that metadata, delegates the loop proof to the stdlib `Spec.forIn_loop`, and restores the
metadata only around the generated strict-decrease proposition. It does not define separate loop
semantics.
-/
@[spec 1200]
theorem whileLoopWithNamedMeasure
    {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Lean.Order.MonadTail m]
    [Assertion Pred] [∀ P : Pred, Lean.Order.PreservesSup (Lean.Order.meet P)]
    [Assertion EPred] [WPMonad m Pred EPred]
    {β : Type u} {l : Lean.Loop} {init : β}
    {inv : β ⊕ β → Pred} {measure : β → Named.Measure}
    {f : Unit → β → m (ForInStep β)} {einv : EPred}
    (step : ∀ b,
      Std.Internal.Do.Triple (f () b)
        (inv (.inl b))
        (fun r => match r with
          | .yield b' =>
              match measure b, measure b' with
              | ⟨name, stx, current⟩, ⟨_, _, next⟩ =>
                  ⌜Named.mk name stx (next < current)⌝ ⊓ inv (.inl b')
          | .done b' => inv (.inr b'))
        einv) :
    Std.Internal.Do.Triple
      (Std.Internal.Do.Gadget.forInLoopWithInvariantAndVariant
        l init f (some (Std.Internal.Do.RepeatInvariant.mk inv)) (some measure))
      (inv (.inl init))
      (fun b => inv (.inr b))
      einv := by
  let loopMeasure := Std.Internal.Do.RepeatVariant.ofMeasure (Pred := Pred)
    (fun b => (measure b).value)
  have step' : ∀ b (mb : loopMeasure.γ),
      Std.Internal.Do.Triple (f () b)
        (loopMeasure.EvalsTo b mb ⊓ inv (.inl b))
        (fun r => match r with
          | .yield b' => loopMeasure.EvalsBelow b' mb ⊓ inv (.inl b')
          | .done b' => inv (.inr b'))
        einv := by
    intro b mb
    apply Std.Internal.Do.Triple.intro
    apply Std.Internal.Do.CompleteLattice.ofProp_meet_le_left
    intro h
    subst mb
    have natRel (a b : Nat) : WellFoundedRelation.rel a b = (a < b) := rfl
    simpa [Named.mk_eq, loopMeasure,
      Std.Internal.Do.RepeatVariant.evalsBelow_ofMeasure, natRel] using (step b).le_wp
  unfold Std.Internal.Do.Gadget.forInLoopWithInvariantAndVariant
  exact Std.Internal.Do.Spec.forIn_loop loopMeasure inv einv step'

end Velvet2.Spec
