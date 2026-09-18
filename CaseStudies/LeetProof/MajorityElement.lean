module

public import Velvet
public meta import Velvet

/-!
## Program description

Given an array `nums` of size `n`, return the majority element.
The majority element is the element that appears strictly more than `⌊n / 2⌋` times.
You may assume that the majority element always exists in the array.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace MajorityElement

section Specs

public def majorityThreshold (n : Nat) : Nat :=
  n / 2

public def isMajority (nums : Array Int) (x : Int) : Prop :=
  nums.count x > majorityThreshold nums.size

public def precondition (nums : Array Int) : Prop :=
  ∃ x : Int, isMajority nums x

public def postcondition (nums : Array Int) (result : Int) : Prop :=
  isMajority nums result ∧
  (∀ y : Int, isMajority nums y → y = result)

end Specs

section Implementation

method majorityElement (nums : Array Int)
  returns (result : Int)
  requires valid: precondition nums
  ensures majority: postcondition nums result
do
  let mut i : Nat := 0
  let mut candidate : Int := 0
  let mut count : Nat := 0
  while' scanning: i < nums.size
    invariant bounds: i ≤ nums.size
    invariant accounting: ∃ p : Nat,
      i = 2 * p + count ∧
      ∀ v : Int, (nums.toList.take i).count v ≤ p + (if v = candidate then count else 0)
    decreasing remaining: nums.size - i
    done_with done: i = nums.size
  do
    let x : Int := nums[i]!
    if is_zero: count = 0 then
      candidate := x
      count := 1
    else if is_cand: x = candidate then
      count := count + 1
    else
      count := count - 1
    i := i + 1
  return candidate

end Implementation

section Proof

theorem count_take_succ (nums : Array Int) (i : Nat) (x : Int) (hi : i < nums.size) :
    (nums.toList.take (i + 1)).count x =
      (nums.toList.take i).count x + if nums[i]! = x then 1 else 0 := by
  have hi_len : i < nums.toList.length := by simpa using hi
  rw [List.take_succ_eq_append_getElem hi_len]
  rw [List.count_append]
  simp [getElem!_pos nums i hi]
  by_cases h : nums[i] = x
  · simp [h]
  · simp [h]

theorem take_size_count (nums : Array Int) (x : Int) :
    (nums.toList.take nums.size).count x = nums.count x := by
  have hlen : nums.toList.length ≤ nums.size := by simp
  rw [List.take_of_length_le hlen, ← Array.count_toList]

theorem step_zero_preserves_accounting (nums : Array Int) (i : Nat) (candidate : Int) (count : Nat)
    (hi : i < nums.size) (hzero : count = 0)
    (hacc : ∃ p : Nat, i = 2 * p + count ∧ ∀ v : Int, (nums.toList.take i).count v ≤ p + if v = candidate then count else 0) :
    ∃ p : Nat, i + 1 = 2 * p + 1 ∧ ∀ v : Int, (nums.toList.take (i + 1)).count v ≤ p + if v = nums[i]! then 1 else 0 := by
  subst hzero
  obtain ⟨p, hi_eq, hbound⟩ := hacc
  refine ⟨p, by omega, ?_⟩
  intro v
  rw [count_take_succ nums i v hi]
  have hb := hbound v
  by_cases hv : nums[i]! = v
  · subst hv
    simp at hb ⊢
    omega
  · simp [hv] at hb ⊢
    omega

theorem step_same_preserves_accounting (nums : Array Int) (i : Nat) (candidate : Int) (count : Nat)
    (hi : i < nums.size)
    (hacc : ∃ p : Nat, i = 2 * p + count ∧ ∀ v : Int, (nums.toList.take i).count v ≤ p + if v = candidate then count else 0)
    (hx : nums[i]! = candidate) :
    ∃ p : Nat, i + 1 = 2 * p + (count + 1) ∧ ∀ v : Int, (nums.toList.take (i + 1)).count v ≤ p + if v = candidate then count + 1 else 0 := by
  obtain ⟨p, hi_eq, hbound⟩ := hacc
  refine ⟨p, by omega, ?_⟩
  intro v
  rw [count_take_succ nums i v hi]
  have hb := hbound v
  by_cases hv : v = candidate
  · subst hv
    simp [hx] at hb ⊢
    omega
  · have hneq : nums[i]! ≠ v := by rw [hx]; exact Ne.symm hv
    simp [hv, hneq] at hb ⊢
    omega

theorem step_diff_preserves_accounting (nums : Array Int) (i : Nat) (candidate : Int) (count : Nat)
    (hi : i < nums.size) (hcount_pos : count ≠ 0)
    (hacc : ∃ p : Nat, i = 2 * p + count ∧ ∀ v : Int, (nums.toList.take i).count v ≤ p + if v = candidate then count else 0)
    (hx : nums[i]! ≠ candidate) :
    ∃ p : Nat, i + 1 = 2 * p + (count - 1) ∧ ∀ v : Int, (nums.toList.take (i + 1)).count v ≤ p + if v = candidate then count - 1 else 0 := by
  obtain ⟨p, hi_eq, hbound⟩ := hacc
  refine ⟨p + 1, by omega, ?_⟩
  intro v
  rw [count_take_succ nums i v hi]
  have hb := hbound v
  by_cases hv : v = candidate
  · subst hv
    simp [hx] at hb ⊢
    omega
  · by_cases hxv : nums[i]! = v
    · subst hxv
      simp [hv] at hb ⊢
      omega
    · simp [hv, hxv] at hb ⊢
      omega

theorem exit_satisfies_postcondition (nums : Array Int) (candidate : Int) (count : Nat) (i : Nat)
    (hpre : precondition nums) (hdone : i = nums.size)
    (hacc : ∃ p : Nat, i = 2 * p + count ∧ ∀ v : Int, (nums.toList.take i).count v ≤ p + if v = candidate then count else 0) :
    postcondition nums candidate := by
  obtain ⟨p, hi_eq, hbound⟩ := hacc
  subst hdone
  have hp_le : p ≤ majorityThreshold nums.size := by
    unfold majorityThreshold
    omega
  have hnot_majority : ∀ v : Int, v ≠ candidate → nums.count v ≤ majorityThreshold nums.size := by
    intro v hv
    have hb := hbound v
    simp [hv] at hb
    rw [← take_size_count]
    exact Nat.le_trans hb hp_le
  obtain ⟨x, hx_maj⟩ := hpre
  have hx_eq : x = candidate := by
    by_cases heq : x = candidate
    · exact heq
    · have := hnot_majority x heq
      unfold isMajority at hx_maj
      omega
  have hcand_maj : isMajority nums candidate := by
    rw [← hx_eq]
    exact hx_maj
  unfold postcondition
  refine ⟨hcand_maj, ?_⟩
  intro y hy
  by_cases heq : y = candidate
  · exact heq
  · have := hnot_majority y heq
    unfold isMajority at hy
    omega

prove_correct majorityElement by
  velvet_vcgen [majorityElement, postcondition] with try finish
  case accounting =>
    refine ⟨0, by omega, fun _ => by simp⟩
  case accounting =>
    rename_i nums
    exact step_zero_preserves_accounting nums i candidate count scanning is_zero accounting
  case accounting =>
    rename_i nums
    exact step_same_preserves_accounting nums i candidate count scanning accounting is_cand
  case accounting =>
    rename_i nums
    have hpos : count ≠ 0 := by omega
    exact step_diff_preserves_accounting nums i candidate count scanning hpos accounting is_cand
  case majority =>
    rename_i nums
    exact exit_satisfies_postcondition nums candidate count i valid done accounting

end Proof

end MajorityElement
