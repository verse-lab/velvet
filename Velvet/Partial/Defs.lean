import Velvet.Specs
import Std.WP
import Std.WP.Triple.SpecLemmas

open Std.WP
open Std.WP.Assertion
open Lean.Order

universe u u₁ u₂ v w

namespace Velvet

/-- Typeclass for monads whose weakest precondition operator is continuous with respect to CCPO chain limits
(fixed-point admissibility). This supports partial correctness verification of possibly divergent recursive loops. -/
class WPPartial (m : Type u → Type v) (Pred : Type u₁) (EPred : Type u₂)
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ α, CCPO (m α)] where
  csup_lift {α : Type u} {c : m α → Prop} (hc : chain c) (hne : ∃ x, c x) (Q : α → Pred) (E : EPred) :
    (⨅ (x : {x : m α // c x}), wp x.val Q E) ⊑ wp (CCPO.csup hc) Q E

theorem emptyChain {α : Sort u} [PartialOrder α] : chain (fun (_ : α) => False) :=
  fun _ _ h => False.elim h

theorem admissible_triple_wp
    {Pred : Type u₁} {EPred : Type u₂}
    {β : Type u} {m : Type u → Type v}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [WPPartial m Pred EPred]
    (pre : Pred) (post : β → Pred) (epost : EPred)
    (hbot : pre ⊑ wp (CCPO.csup (α := m β) (c := fun _ => False) emptyChain) post epost := by intros; try trivial) :
    admissible (fun (c : m β) => pre ⊑ wp c post epost) := by
  intro c hc h
  by_cases hne : ∃ x, c x
  · apply PartialOrder.rel_trans _ (WPPartial.csup_lift hc hne post epost)
    apply le_iInf
    rintro ⟨x, hx⟩
    exact h x hx
  · have h_eq : (CCPO.csup hc) = CCPO.csup (α := m β) (c := fun _ => False) emptyChain := by
      apply PartialOrder.rel_antisymm
      · apply csup_le hc
        intro x hx
        exact False.elim (hne ⟨x, hx⟩)
      · apply csup_le emptyChain
        intro x hx
        exact False.elim hx
    rw [h_eq]
    exact hbot

end Velvet
