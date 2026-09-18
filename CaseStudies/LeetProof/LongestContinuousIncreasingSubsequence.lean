module

public import Velvet
public meta import Velvet

/-!
## Program description

Given an unsorted array of integers `nums`, return the length of the longest
continuous increasing subsequence (i.e. subarray). The subsequence must be
strictly increasing.

A continuous increasing subsequence is defined by two indices `l` and `r`
(`l < r`) such that it is `[nums[l], nums[l + 1], ..., nums[r - 1]]` and for
each `l <= i < r - 1`, `nums[i] < nums[i + 1]`.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace LongestContinuousIncreasingSubsequence

section Specs

public def segInBounds (nums : Array Int) (l : Nat) (len : Nat) : Prop :=
  l + len ≤ nums.size

public def segNonempty (len : Nat) : Prop :=
  1 ≤ len

public def segStrictlyIncreasing (nums : Array Int) (l : Nat) (len : Nat) : Prop :=
  segNonempty len ∧
  segInBounds nums l len ∧
  (∀ (i : Nat), i + 1 < len → nums[l + i]! < nums[l + i + 1]!)

public def precondition (nums : Array Int) : Prop :=
  nums.size > 0

public def postcondition (nums : Array Int) (result : Nat) : Prop :=
  result ≥ 1 ∧
  result ≤ nums.size ∧
  (∃ (l : Nat), segStrictlyIncreasing nums l result) ∧
  (∀ (l : Nat) (len : Nat), segStrictlyIncreasing nums l len → len ≤ result)

end Specs

section Implementation

method findLengthOfLCIS (nums : Array Int)
  returns (result : Nat)
  requires nonempty: precondition nums
  ensures longest_subsequence: postcondition nums result
do
  let n := nums.size
  let mut best : Nat := 1
  let mut curr : Nat := 1
  let mut i : Nat := 1
  while' scanning: i < n
    invariant inv_i_bounds: 1 ≤ i ∧ i ≤ n
    invariant inv_curr_range: 1 ≤ curr ∧ curr ≤ i
    invariant inv_best_range: 1 ≤ best ∧ best ≤ i
    invariant inv_best_ge_curr: curr ≤ best
    invariant inv_curr_segment: segStrictlyIncreasing nums (i - curr) curr ∧ (i - curr) + curr = i
    invariant inv_curr_max_end: ∀ (l : Nat) (len : Nat), segStrictlyIncreasing nums l len ∧ l + len = i → len ≤ curr
    invariant inv_best_exists: ∃ l : Nat, segStrictlyIncreasing nums l best ∧ l + best ≤ i
    invariant inv_best_max: ∀ (l : Nat) (len : Nat), segStrictlyIncreasing nums l len ∧ l + len ≤ i → len ≤ best
    decreasing remaining: n - i
    done_with done: i = n
  do
    if inc: nums[i - 1]! < nums[i]! then
      curr := curr + 1
    else
      curr := 1
    if better: best < curr then
      best := curr
    i := i + 1
  return best

end Implementation

section Proof

theorem segStrictlyIncreasing_single (nums : Array Int) (l : Nat) (hl : l + 1 ≤ nums.size) :
    segStrictlyIncreasing nums l 1 := by
  unfold segStrictlyIncreasing segNonempty segInBounds
  refine ⟨by omega, hl, fun _ hj => by omega⟩

theorem segStrictlyIncreasing_extend (nums : Array Int) (curr i : Nat)
    (hcurr_ge : 1 ≤ curr)
    (hcurr_le : curr ≤ i)
    (hseg : segStrictlyIncreasing nums (i - curr) curr)
    (hbound : i < nums.size)
    (hstep : nums[i - 1]! < nums[i]!) :
    segStrictlyIncreasing nums (i + 1 - (curr + 1)) (curr + 1) ∧
      (i + 1 - (curr + 1)) + (curr + 1) = i + 1 := by
  have heq : i + 1 - (curr + 1) = i - curr := by omega
  refine ⟨?_, by omega⟩
  rw [heq]
  unfold segStrictlyIncreasing at *
  rcases hseg with ⟨_, _, hinc⟩
  refine ⟨by unfold segNonempty; omega, by unfold segInBounds; omega, ?_⟩
  intro j hj
  by_cases hj_last : j + 1 = curr
  · rw [show i - curr + j = i - 1 by omega]
    rw [show i - 1 + 1 = i by omega]
    exact hstep
  · have hj_lt : j + 1 < curr := by omega
    exact hinc j hj_lt

theorem curr_max_end_extend (nums : Array Int) (curr i : Nat)
    (hmax : ∀ (l len : Nat), segStrictlyIncreasing nums l len ∧ l + len = i → len ≤ curr)
    (l len : Nat)
    (hseg : segStrictlyIncreasing nums l len)
    (hend : l + len = i + 1) :
    len ≤ curr + 1 := by
  by_cases hlen_le1 : len ≤ 1
  · omega
  · rcases hseg with ⟨_, hbound, hinc⟩
    unfold segInBounds at hbound
    have hseg_pred : segStrictlyIncreasing nums l (len - 1) := by
      unfold segStrictlyIncreasing segNonempty segInBounds
      refine ⟨by omega, by omega, fun j hj => hinc j (by omega)⟩
    have hend_pred : l + (len - 1) = i := by omega
    have hle_curr := hmax l (len - 1) ⟨hseg_pred, hend_pred⟩
    omega

theorem curr_max_end_reset (nums : Array Int) (i : Nat)
    (hnot_inc : ¬ nums[i - 1]! < nums[i]!)
    (l len : Nat)
    (hseg : segStrictlyIncreasing nums l len)
    (hend : l + len = i + 1) :
    len ≤ 1 := by
  by_cases hle : len ≤ 1
  · exact hle
  · rcases hseg with ⟨_, _, hinc⟩
    have hj : len - 2 + 1 < len := by omega
    have hstep := hinc (len - 2) hj
    rw [show l + (len - 2) = i - 1 by omega] at hstep
    rw [show i - 1 + 1 = i by omega] at hstep
    exact False.elim (hnot_inc hstep)

theorem best_max_step_better (nums : Array Int) (best curr i : Nat)
    (hbetter : best < curr + 1)
    (hcurr_max : ∀ (l len : Nat), segStrictlyIncreasing nums l len ∧ l + len = i → len ≤ curr)
    (hbest_max : ∀ (l len : Nat), segStrictlyIncreasing nums l len ∧ l + len ≤ i → len ≤ best)
    (l len : Nat)
    (hseg : segStrictlyIncreasing nums l len)
    (hle : l + len ≤ i + 1) :
    len ≤ curr + 1 := by
  by_cases hend : l + len = i + 1
  · exact curr_max_end_extend nums curr i hcurr_max l len hseg hend
  · have hle_i : l + len ≤ i := by omega
    have hle_best := hbest_max l len ⟨hseg, hle_i⟩
    omega

theorem best_max_step_not_better (nums : Array Int) (best curr i : Nat)
    (hnot_better : ¬ best < curr + 1)
    (hcurr_max : ∀ (l len : Nat), segStrictlyIncreasing nums l len ∧ l + len = i → len ≤ curr)
    (hbest_max : ∀ (l len : Nat), segStrictlyIncreasing nums l len ∧ l + len ≤ i → len ≤ best)
    (l len : Nat)
    (hseg : segStrictlyIncreasing nums l len)
    (hle : l + len ≤ i + 1) :
    len ≤ best := by
  by_cases hend : l + len = i + 1
  · have hlen_curr := curr_max_end_extend nums curr i hcurr_max l len hseg hend
    omega
  · have hle_i : l + len ≤ i := by omega
    exact hbest_max l len ⟨hseg, hle_i⟩

theorem best_max_step_reset (nums : Array Int) (best i : Nat)
    (hbest_ge : 1 ≤ best)
    (hnot_inc : ¬ nums[i - 1]! < nums[i]!)
    (hbest_max : ∀ (l len : Nat), segStrictlyIncreasing nums l len ∧ l + len ≤ i → len ≤ best)
    (l len : Nat)
    (hseg : segStrictlyIncreasing nums l len)
    (hle : l + len ≤ i + 1) :
    len ≤ best := by
  by_cases hend : l + len = i + 1
  · have hlen1 := curr_max_end_reset nums i hnot_inc l len hseg hend
    omega
  · have hle_i : l + len ≤ i := by omega
    exact hbest_max l len ⟨hseg, hle_i⟩

theorem postcondition_of_loop_exit (nums : Array Int) (best _curr i : Nat)
    (hdone : i = nums.size)
    (hbest_range : 1 ≤ best ∧ best ≤ i)
    (hbest_exists : ∃ l, segStrictlyIncreasing nums l best ∧ l + best ≤ i)
    (hbest_max : ∀ (l len : Nat), segStrictlyIncreasing nums l len ∧ l + len ≤ i → len ≤ best) :
    postcondition nums best := by
  subst hdone
  rcases hbest_exists with ⟨l, hseg, _⟩
  refine ⟨hbest_range.1, hbest_range.2, ⟨l, hseg⟩, ?_⟩
  intro l' len' hseg'
  have hb := hseg'.2.1
  unfold segInBounds at hb
  exact hbest_max l' len' ⟨hseg', hb⟩

prove_correct findLengthOfLCIS by
  velvet_vcgen [findLengthOfLCIS, precondition, postcondition] with try finish
  case inv_i_bounds =>
    unfold precondition at nonempty
    omega
  case inv_curr_segment =>
    rename_i nums
    have hsz : 0 + 1 ≤ nums.size := by
      unfold precondition at nonempty
      omega
    exact segStrictlyIncreasing_single nums 0 hsz
  case inv_best_exists =>
    rename_i nums
    have hsz : 0 + 1 ≤ nums.size := by
      unfold precondition at nonempty
      omega
    exact ⟨0, segStrictlyIncreasing_single nums 0 hsz, by omega⟩
  case longest_subsequence =>
    rename_i nums
    exact postcondition_of_loop_exit nums best curr i done inv_best_range inv_best_exists inv_best_max
  case inv_curr_segment =>
    rename_i nums
    exact segStrictlyIncreasing_extend nums curr i inv_curr_range.1 inv_curr_range.2 inv_curr_segment.1 scanning inc
  case inv_curr_max_end =>
    rename_i nums
    intro l len ⟨hseg, hend⟩
    exact curr_max_end_extend nums curr i inv_curr_max_end l len hseg hend
  case inv_best_exists =>
    rename_i nums
    have hext := segStrictlyIncreasing_extend nums curr i inv_curr_range.1 inv_curr_range.2 inv_curr_segment.1 scanning inc
    refine ⟨i + 1 - (curr + 1), hext.1, by omega⟩
  case inv_best_max =>
    rename_i nums
    intro l len ⟨hseg, hle⟩
    exact best_max_step_better nums best curr i better inv_curr_max_end inv_best_max l len hseg hle
  case inv_curr_segment =>
    rename_i nums
    exact segStrictlyIncreasing_extend nums curr i inv_curr_range.1 inv_curr_range.2 inv_curr_segment.1 scanning inc
  case inv_curr_max_end =>
    rename_i nums
    intro l len ⟨hseg, hend⟩
    exact curr_max_end_extend nums curr i inv_curr_max_end l len hseg hend
  case inv_best_max =>
    rename_i nums
    intro l len ⟨hseg, hle⟩
    exact best_max_step_not_better nums best curr i better inv_curr_max_end inv_best_max l len hseg hle
  case inv_curr_segment =>
    rename_i nums
    exact ⟨segStrictlyIncreasing_single nums i (by omega), by omega⟩
  case inv_curr_max_end =>
    rename_i nums
    intro l len ⟨hseg, hend⟩
    exact curr_max_end_reset nums i inc l len hseg hend
  case inv_best_max =>
    rename_i nums
    intro l len ⟨hseg, hle⟩
    exact best_max_step_reset nums best i inv_best_range.1 inc inv_best_max l len hseg hle

end Proof

end LongestContinuousIncreasingSubsequence
