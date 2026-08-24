import Velvet2.Specs
import Std.Internal.Do
import Std.Internal.Do.Order.Basic
import Std.Internal.Do.Triple.SpecLemmas

open Std.Internal
open Std.Internal.Do
open Std.Internal.Do.Assertion
open Lean.Order
open Std.Internal.Do.CompleteLattice

universe u u₁ u₂ v w

namespace Velvet2

/-- Typeclass for monads whose weakest precondition operator is continuous with respect to CCPO chain limits
(fixed-point admissibility). This supports partial correctness verification of possibly divergent recursive loops. -/
class WPPartial (m : Type u → Type v) (Pred : Type u₁) (EPred : Type u₂)
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ α, CCPO (m α)] where
  csup_lift {α : Type u} {c : m α → Prop} (hc : chain c) (Q : α → Pred) (E : EPred) :
    (⨅ (x : {x : m α // c x}), wp x.val Q E) ⊑ wp (CCPO.csup hc) Q E

theorem admissible_triple_wp
    {Pred : Type u₁} {EPred : Type u₂}
    {β : Type u} {m : Type u → Type v}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ α, CCPO (m α)] [WPPartial m Pred EPred]
    (pre : Pred) (post : β → Pred) (epost : EPred) :
    admissible (fun (c : m β) => pre ⊑ wp c post epost) := by
  intro c hc h
  apply PartialOrder.rel_trans _ (WPPartial.csup_lift hc post epost)
  apply le_iInf
  rintro ⟨x, hx⟩
  exact h x hx

end Velvet2
