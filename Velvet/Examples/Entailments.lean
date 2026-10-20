module

public import Velvet
public meta import Velvet

open Std.WP Lean.Order

/-!
# Entailment goals

`velvet_vcgen` also proves an entailment `pre ⊑ rhs` that contains no program: it lifts the
precondition into hypotheses, splits `⊓`, and introduces state arguments. Fixpoint induction for a
`method rec` leaves such goals (see `Recursion.lean`).
-/

namespace Velvet.Examples.Entailments

example (P Q : Prop) : (⌜P ∧ Q⌝ : Prop) ⊑ (⌜P⌝ ⊓ ⌜Q⌝) := by
  velvet_vcgen with finish

example : (fun s : Nat => (⌜s = 1⌝ : Prop)) ⊑ (fun s => (⌜s > 0⌝ ⊓ ⌜s < 2⌝ : Prop)) := by
  velvet_vcgen with finish

/- What does not follow is left as a VC. -/
/--
error: unsolved goals
case vc1
P Q : Prop
a✝ : P
⊢ Q
-/
#guard_msgs in
example (P Q : Prop) : (⌜P⌝ : Prop) ⊑ (⌜P⌝ ⊓ ⌜Q⌝) := by
  velvet_vcgen

end Velvet.Examples.Entailments
