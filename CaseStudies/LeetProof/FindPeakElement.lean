module

public import Velvet
public meta import Velvet

/-!
## Program description

A peak element is an element that is strictly greater than its neighbors.

Given a 0-indexed integer array `nums`, find a peak element, and return its
index. If the array contains multiple peaks, return the index to any of the
peaks.

You may imagine that `nums[-1] = nums[n] = -∞`. In other words, an element is
always considered to be strictly greater than a neighbor that is outside the
array.

Adjacent elements are assumed to be distinct.

The program is expected to run in O(log n) time and O(1) extra space.
-/

namespace FindPeakElement

section Specs

public def IsPeakIndex (nums : Array Int) (i : Nat) : Prop :=
  i < nums.size ∧
  (0 < i → nums[i]! > nums[i - 1]!) ∧
  (i + 1 < nums.size → nums[i]! > nums[i + 1]!)

public def precondition (nums : Array Int) : Prop :=
  nums.size > 0 ∧
  (∀ i : Nat, i + 1 < nums.size → nums[i]! ≠ nums[i + 1]!)

public def postcondition (nums : Array Int) (result : Nat) : Prop :=
  IsPeakIndex nums result

end Specs

section Implementation

method findPeakElement (nums : Array Int)
  returns (result : Nat)
  requires valid: precondition nums
  ensures is_peak: postcondition nums result
do
  let n := nums.size
  let mut lo : Nat := 0
  let mut hi : Nat := n - 1
  while searching: lo < hi
    invariant bounds: lo ≤ hi ∧ hi < n
    invariant left_slope: lo = 0 ∨ nums[lo]! > nums[lo - 1]!
    invariant right_slope: hi = n - 1 ∨ nums[hi]! > nums[hi + 1]!
    decreasing remaining: hi - lo
    done_with done: lo = hi
  do
    let mid : Nat := lo + (hi - lo) / 2
    if go_right: nums[mid]! < nums[mid + 1]! then
      lo := mid + 1
    else
      hi := mid
  return lo

end Implementation

section Proof

theorem exit_is_peak (nums : Array Int) (lo hi : Nat)
    (hbounds : lo ≤ hi ∧ hi < nums.size)
    (hleft : lo = 0 ∨ nums[lo]! > nums[lo - 1]!)
    (hright : hi = nums.size - 1 ∨ nums[hi]! > nums[hi + 1]!)
    (hdone : lo = hi) :
    IsPeakIndex nums lo := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hlo
    cases hleft with
    | inl h0 => omega
    | inr hgt => exact hgt
  · intro hnext
    cases hright with
    | inl hlast => omega
    | inr hgt =>
      rw [hdone]
      exact hgt

theorem right_slope_preserved (nums : Array Int) (mid : Nat)
    (hpre : precondition nums)
    (hmid1 : mid + 1 < nums.size)
    (hnot_right : ¬ nums[mid]! < nums[mid + 1]!) :
    mid = nums.size - 1 ∨ nums[mid]! > nums[mid + 1]! := by
  right
  have hne := hpre.2 mid hmid1
  omega

prove_correct findPeakElement by
  velvet_vcgen [findPeakElement, precondition, postcondition, IsPeakIndex] with try finish
  case bounds =>
    unfold precondition at valid
    omega
  case is_peak =>
    rename_i nums
    exact exit_is_peak nums lo hi bounds left_slope right_slope done
  case right_slope =>
    rename_i nums
    exact right_slope_preserved nums (lo + (hi - lo) / 2) valid (by omega) go_right

end Proof

end FindPeakElement
