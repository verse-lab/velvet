module

public import Velvet
public meta import Velvet

/-!
## Program description

Given an array of line heights, return the maximum water area.

1. The input is an array `height` of nonnegative integers, interpreted as
   vertical lines at x-coordinates `0 .. n - 1`.
2. For any two distinct indices `i < j`, a container can be formed with width
   `j - i`.
3. The container height is limited by the shorter line:
   `min height[i] height[j]`.
4. The area for a pair `(i, j)` is
   `(j - i) * min height[i] height[j]`.
5. The result is the maximum area over all index pairs with `i < j`.
6. We require at least two elements, since otherwise no valid container exists.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace ContainerWithMostWater

section Specs

/-- The area contributed by indices `i` and `j`. Specifications only use this
definition when `i < j < height.size`. -/

public def pairArea (height : Array Nat) (i j : Nat) : Nat :=
  (j - i) * Nat.min height[i]! height[j]!

/-- At least two vertical lines are available. -/

public def precondition (height : Array Nat) : Prop :=
  height.size ≥ 2

/-- The result is attained by a valid pair and bounds the area of every valid
pair. -/

public def postcondition (height : Array Nat) (result : Nat) : Prop :=
  (∃ i j, i < j ∧ j < height.size ∧ pairArea height i j = result) ∧
  (∀ i j, i < j → j < height.size → pairArea height i j ≤ result)

end Specs

section Implementation

/-- `best` is the area of an actual container. -/

public def Achievable (height : Array Nat) (best : Nat) : Prop :=
  ∃ i j, i < j ∧ j < height.size ∧ pairArea height i j = best

/-- Every pair already excluded by the two pointers is no better than `best`. -/

public def DiscardedBound
    (height : Array Nat) (left right best : Nat) : Prop :=
  ∀ i j, i < j → j < height.size →
    (i < left ∨ right < j) → pairArea height i j ≤ best

method maxArea (height : Array Nat)
  returns (result : Nat)
  requires enough_lines: precondition height
  ensures maximum_area: postcondition height result
do
  let mut left : Nat := 0
  let mut right : Nat := height.size - 1
  let mut best : Nat := pairArea height left right
  while pointers_apart: left < right
    invariant left_in_bounds: left < height.size
    invariant right_in_bounds: right < height.size
    invariant pointers_ordered: left ≤ right
    invariant best_is_achievable: Achievable height best
    invariant discarded_pairs_bounded: DiscardedBound height left right best
    decreasing remaining_width: right - left
    done_with pointers_meet: left = right
  do
    let area := pairArea height left right
    best := Nat.max best area
    if left_shorter: height[left]! ≤ height[right]! then
      left := left + 1
    else
      right := right - 1
  return best

end Implementation

section Proof

theorem left_pair_le_endpoints
    (height : Array Nat) (left j right : Nat)
    (hj : j ≤ right) (hh : height[left]! ≤ height[right]!) :
    pairArea height left j ≤ pairArea height left right := by
  unfold pairArea
  apply Nat.mul_le_mul
  · omega
  · simpa [Nat.min_eq_left hh] using
      (Nat.min_le_left height[left]! height[j]!)

theorem right_pair_le_endpoints
    (height : Array Nat) (left i right : Nat)
    (hi : left ≤ i) (hh : height[right]! ≤ height[left]!) :
    pairArea height i right ≤ pairArea height left right := by
  unfold pairArea
  apply Nat.mul_le_mul
  · omega
  · simpa [Nat.min_eq_right hh] using
      (Nat.min_le_right height[i]! height[right]!)

theorem achievable_max_left
    {height : Array Nat} {left right best : Nat}
    (hbest : Achievable height best)
    (hlt : left < right) (hr : right < height.size) :
    Achievable height (Nat.max best (pairArea height left right)) := by
  by_cases h : best ≤ pairArea height left right
  · refine ⟨left, right, hlt, hr, ?_⟩
    simp [Nat.max_eq_right h]
  · obtain ⟨i, j, hij, hj, harea⟩ := hbest
    refine ⟨i, j, hij, hj, ?_⟩
    have hmax : Nat.max best (pairArea height left right) = best :=
      Nat.max_eq_left (by omega)
    exact harea.trans hmax.symm

theorem discard_left
    {height : Array Nat} {left right best : Nat}
    (hdiscarded : DiscardedBound height left right best)
    (_hlt : left < right)
    (hh : height[left]! ≤ height[right]!) :
    DiscardedBound height (left + 1) right
      (Nat.max best (pairArea height left right)) := by
  intro i j hij hj houtside
  by_cases hold : i < left ∨ right < j
  · exact Nat.le_trans (hdiscarded i j hij hj hold) (Nat.le_max_left _ _)
  · have hi : i = left := by omega
    have hjr : j ≤ right := by omega
    subst i
    exact Nat.le_trans (left_pair_le_endpoints height left j right hjr hh)
      (Nat.le_max_right _ _)

theorem discard_right
    {height : Array Nat} {left right best : Nat}
    (hdiscarded : DiscardedBound height left right best)
    (_hlt : left < right)
    (hh : height[right]! ≤ height[left]!) :
    DiscardedBound height left (right - 1)
      (Nat.max best (pairArea height left right)) := by
  intro i j hij hj houtside
  by_cases hold : i < left ∨ right < j
  · exact Nat.le_trans (hdiscarded i j hij hj hold) (Nat.le_max_left _ _)
  · have hi : left ≤ i := by omega
    have hjr : j = right := by omega
    subst j
    exact Nat.le_trans (right_pair_le_endpoints height left i right hi hh)
      (Nat.le_max_right _ _)

theorem discarded_at_meeting
    {height : Array Nat} {left right best : Nat}
    (hmeet : left = right)
    (hdiscarded : DiscardedBound height left right best) :
    ∀ i j, i < j → j < height.size → pairArea height i j ≤ best := by
  intro i j hij hj
  apply hdiscarded i j hij hj
  omega

prove_correct maxArea by
  velvet_vcgen [maxArea, precondition, postcondition, Achievable, DiscardedBound] with try finish
  case left_in_bounds =>
    rename_i height
    unfold precondition at enough_lines
    omega
  case right_in_bounds =>
    rename_i height
    unfold precondition at enough_lines
    omega
  case best_is_achievable =>
    rename_i height
    unfold precondition at enough_lines
    refine ⟨0, height.size - 1, by omega, by omega, rfl⟩
  case discarded_pairs_bounded =>
    unfold DiscardedBound
    intro i j hij hj houtside
    omega
  case maximum_area =>
    exact ⟨best_is_achievable,
      discarded_at_meeting pointers_meet discarded_pairs_bounded⟩
  case best_is_achievable =>
    exact achievable_max_left best_is_achievable pointers_apart right_in_bounds
  case discarded_pairs_bounded =>
    exact discard_left discarded_pairs_bounded pointers_apart left_shorter
  case best_is_achievable =>
    exact achievable_max_left best_is_achievable pointers_apart right_in_bounds
  case discarded_pairs_bounded =>
    apply discard_right discarded_pairs_bounded pointers_apart
    omega

end Proof

end ContainerWithMostWater
