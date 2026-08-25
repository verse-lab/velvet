import Velvet.Named
import Std.WP

open Std.WP

variable {m : Type u → Type v} {Pred EPred : Type u}

/-- A runtime no-op that introduces an assertion into verification conditions. -/
def assertGadget [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] (_assertion : Pred) : m PUnit := pure ⟨⟩

namespace Velvet.Spec

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

end Velvet.Spec
