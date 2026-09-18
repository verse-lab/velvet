module

public import Velvet
public meta import Velvet
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith

/-!
## Program description

Given a circular integer array `nums` of length `n`, return the maximum possible
sum of a non-empty subarray of `nums`.

A circular array means the end of the array connects to the beginning of the
array. Formally, the next element of `nums[i]` is `nums[(i + 1) % n]` and the
previous element of `nums[i]` is `nums[(i - 1 + n) % n]`.

A subarray may only include each element of the fixed buffer `nums` at most once.
Formally, for a subarray `nums[i], nums[i + 1], ..., nums[j]`, there does not
exist `i ≤ k1, k2 ≤ j` with `k1 % n = k2 % n` and `k1 ≠ k2`.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace MaximumSumCircularSubarray

section Specs

public def circSegmentSum (arr : Array Int) (start : Nat) (len : Nat) : Int :=
  (Finset.range len).sum (fun i => arr[(start + i) % arr.size]!)

public def isValidCircSegment (arr : Array Int) (start : Nat) (len : Nat) : Prop :=
  arr.size > 0 ∧ start < arr.size ∧ 1 ≤ len ∧ len ≤ arr.size

public def precondition (nums : Array Int) : Prop :=
  nums.size > 0

public def postcondition (nums : Array Int) (result : Int) : Prop :=
  (∃ (start : Nat) (len : Nat),
      isValidCircSegment nums start len ∧ circSegmentSum nums start len = result) ∧
  (∀ (start : Nat) (len : Nat),
      isValidCircSegment nums start len → circSegmentSum nums start len ≤ result)

end Specs

section Implementation

public def prefixSum (nums : Array Int) (len : Nat) : Int :=
  (Finset.range len).sum (fun i => nums[i]!)

public def linSum (nums : Array Int) (start len : Nat) : Int :=
  (Finset.range len).sum (fun i => nums[start + i]!)

method maxSumCircularSubarray (nums : Array Int)
  returns (result : Int)
  requires nonempty: precondition nums
  ensures maximum: postcondition nums result
do
  let mut i : Nat := 1
  let mut total : Int := nums[0]!
  let mut curMax : Int := nums[0]!
  let mut maxSum : Int := nums[0]!
  let mut curMin : Int := nums[0]!
  let mut minSum : Int := nums[0]!
  while scanning: i < nums.size
    invariant index_bounds: 1 ≤ i ∧ i ≤ nums.size
    invariant total_val: total = prefixSum nums i
    invariant curMax_achievable:
      ∃ start < i, linSum nums start (i - start) = curMax
    invariant curMax_maximal:
      ∀ start < i, linSum nums start (i - start) ≤ curMax
    invariant maxSum_achievable:
      ∃ start < i, ∃ len, 1 ≤ len ∧ start + len ≤ i ∧ linSum nums start len = maxSum
    invariant maxSum_maximal:
      ∀ start < i, ∀ len, 1 ≤ len → start + len ≤ i → linSum nums start len ≤ maxSum
    invariant curMin_achievable:
      ∃ start < i, linSum nums start (i - start) = curMin
    invariant curMin_minimal:
      ∀ start < i, curMin ≤ linSum nums start (i - start)
    invariant minSum_achievable:
      ∃ start < i, ∃ len, 1 ≤ len ∧ start + len ≤ i ∧ linSum nums start len = minSum
    invariant minSum_minimal:
      ∀ start < i, ∀ len, 1 ≤ len → start + len ≤ i → minSum ≤ linSum nums start len
    decreasing remaining: nums.size - i
    done_with done: i = nums.size
  do
    let x := nums[i]!
    total := total + x
    curMax := max x (curMax + x)
    maxSum := max maxSum curMax
    curMin := min x (curMin + x)
    minSum := min minSum curMin
    i := i + 1
  if all_neg: maxSum < 0 then
    return maxSum
  else
    return max maxSum (total - minSum)

end Implementation

section Proof

@[simp] theorem linSum_zero (arr : Array Int) (start : Nat) : linSum arr start 0 = 0 := by
  unfold linSum
  simp

@[simp] theorem linSum_one (arr : Array Int) (start : Nat) : linSum arr start 1 = arr[start]! := by
  unfold linSum
  simp

theorem linSum_succ (arr : Array Int) (start len : Nat) :
    linSum arr start (len + 1) = linSum arr start len + arr[start + len]! := by
  unfold linSum
  rw [Finset.sum_range_succ]

@[simp] theorem prefixSum_zero (arr : Array Int) : prefixSum arr 0 = 0 := by
  unfold prefixSum
  simp

@[simp] theorem prefixSum_one (arr : Array Int) : prefixSum arr 1 = arr[0]! := by
  unfold prefixSum
  simp

theorem prefixSum_succ (arr : Array Int) (len : Nat) :
    prefixSum arr (len + 1) = prefixSum arr len + arr[len]! := by
  unfold prefixSum
  rw [Finset.sum_range_succ]

theorem prefixSum_eq_linSum_zero (arr : Array Int) (len : Nat) :
    prefixSum arr len = linSum arr 0 len := by
  unfold prefixSum linSum
  simp

lemma circSegmentSum_non_wrap (arr : Array Int) (start len : Nat)
    (h_len : start + len ≤ arr.size) :
    circSegmentSum arr start len = linSum arr start len := by
  unfold circSegmentSum linSum
  have h_mod : ∀ k ∈ Finset.range len, (start + k) % arr.size = start + k := by
    intro k hk
    exact Nat.mod_eq_of_lt (by linarith [Finset.mem_range.mp hk])
  exact Finset.sum_congr rfl (fun k hk => congr_arg (fun x => arr[x]!) (h_mod k hk))

lemma circSegmentSum_wrap (arr : Array Int) (start len : Nat)
    (h_start : start < arr.size) (h_len2 : len ≤ arr.size)
    (h_wrap : arr.size < start + len) :
    circSegmentSum arr start len =
      prefixSum arr arr.size -
      ∑ k ∈ Finset.range (arr.size - len), arr[((start + len) % arr.size + k) % arr.size]! := by
  unfold prefixSum
  have h_split : circSegmentSum arr start len =
      ∑ k ∈ Finset.range (arr.size - start), arr[start + k]! +
      ∑ k ∈ Finset.range (len - (arr.size - start)), arr[k]! := by
    unfold circSegmentSum
    rw [← Finset.sum_range_add_sum_Ico _ (show arr.size - start ≤ len from by omega)]
    rw [Finset.sum_Ico_eq_sum_range]
    congr! 2
    · rw [Nat.mod_eq_of_lt (by linarith [Finset.mem_range.mp ‹_›, Nat.sub_add_cancel h_start.le])]
    · rename_i k hk
      have hk_lt : k < len - (arr.size - start) := Finset.mem_range.mp hk
      have h_idx : (start + (arr.size - start + k)) % arr.size = k := by
        have : start + (arr.size - start + k) = arr.size + k := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [h_idx]
  have h_complement_split : ∑ k ∈ Finset.range (arr.size - len), arr[((start + len) % arr.size + k) % arr.size]! =
      ∑ j ∈ Finset.Ico (start + len - arr.size) start, arr[j]! := by
    have h_complement : ∑ k ∈ Finset.range (arr.size - len), arr[((start + len) % arr.size + k) % arr.size]! =
        ∑ k ∈ Finset.range (arr.size - len), arr[(start + len - arr.size + k) % arr.size]! := by
      simp +decide [Nat.mod_eq_sub_mod (show arr.size ≤ start + len from h_wrap.le)]
    rw [h_complement]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show start - (start + len - arr.size) = arr.size - len by omega]
    exact Finset.sum_congr rfl (fun x hx => by rw [Nat.mod_eq_of_lt (by linarith [Finset.mem_range.mp hx, Nat.sub_add_cancel h_len2, Nat.sub_add_cancel h_wrap.le])])
  have h_total : ∑ j ∈ Finset.range arr.size, arr[j]! =
      ∑ j ∈ Finset.range (start + len - arr.size), arr[j]! +
      ∑ j ∈ Finset.Ico (start + len - arr.size) start, arr[j]! +
      ∑ j ∈ Finset.Ico start arr.size, arr[j]! := by
    rw [Finset.sum_range_add_sum_Ico, Finset.sum_range_add_sum_Ico] <;> omega
  simp_all +decide [Finset.sum_Ico_eq_sum_range]
  grind

lemma circSegmentSum_wrap_complement (arr : Array Int) (start len : Nat)
    (h_start : start < arr.size)
    (h_wrap : arr.size < start + len) (h_len3 : len < arr.size) :
    ∑ k ∈ Finset.range (arr.size - len), arr[((start + len) % arr.size + k) % arr.size]! =
    linSum arr ((start + len) % arr.size) (arr.size - len) := by
  unfold linSum
  have h_mod_eq : ∀ k ∈ Finset.range (arr.size - len),
      ((start + len) % arr.size + k) % arr.size = (start + len) % arr.size + k := by
    intro k hk
    have hk_lt : k < arr.size - len := Finset.mem_range.mp hk
    have h_lt : (start + len) % arr.size + k < arr.size := by
      have : (start + len) % arr.size = start + len - arr.size := by
        rw [Nat.mod_eq_sub_mod h_wrap.le, Nat.mod_eq_of_lt (by omega)]
      omega
    exact Nat.mod_eq_of_lt h_lt
  exact Finset.sum_congr rfl (fun x hx => by rw [h_mod_eq x hx])

lemma curMax_step_achievable (nums : Array Int) (i : Nat) (curMax : Int)
    (h_ach : ∃ start < i, linSum nums start (i - start) = curMax) :
    ∃ start < i + 1, linSum nums start (i + 1 - start) = max nums[i]! (curMax + nums[i]!) := by
  by_cases h : nums[i]! ≤ curMax + nums[i]!
  · obtain ⟨start, hs, hsum⟩ := h_ach
    refine ⟨start, by omega, ?_⟩
    have hsub : i + 1 - start = (i - start) + 1 := by omega
    have hidx : start + (i - start) = i := by omega
    rw [hsub, linSum_succ, hidx, hsum, Int.max_eq_right h]
  · refine ⟨i, by omega, ?_⟩
    have : i + 1 - i = 1 := by omega
    rw [this, linSum_one, Int.max_eq_left (by omega)]

lemma curMax_step_maximal (nums : Array Int) (i : Nat) (curMax : Int)
    (h_max : ∀ start < i, linSum nums start (i - start) ≤ curMax) :
    ∀ start < i + 1, linSum nums start (i + 1 - start) ≤ max nums[i]! (curMax + nums[i]!) := by
  intro start hs
  by_cases heq : start = i
  · have hlen : i + 1 - start = 1 := by omega
    rw [hlen, linSum_one, heq]
    exact Int.le_max_left _ _
  · have hlt : start < i := by omega
    have hsub : i + 1 - start = (i - start) + 1 := by omega
    have hidx : start + (i - start) = i := by omega
    rw [hsub, linSum_succ, hidx]
    have hle : linSum nums start (i - start) + nums[i]! ≤ curMax + nums[i]! :=
      Int.add_le_add_right (h_max start hlt) _
    exact Int.le_trans hle (Int.le_max_right _ _)

lemma curMin_step_achievable (nums : Array Int) (i : Nat) (curMin : Int)
    (h_ach : ∃ start < i, linSum nums start (i - start) = curMin) :
    ∃ start < i + 1, linSum nums start (i + 1 - start) = min nums[i]! (curMin + nums[i]!) := by
  by_cases h : curMin + nums[i]! ≤ nums[i]!
  · obtain ⟨start, hs, hsum⟩ := h_ach
    refine ⟨start, by omega, ?_⟩
    have hsub : i + 1 - start = (i - start) + 1 := by omega
    have hidx : start + (i - start) = i := by omega
    rw [hsub, linSum_succ, hidx, hsum, Int.min_eq_right h]
  · refine ⟨i, by omega, ?_⟩
    have : i + 1 - i = 1 := by omega
    rw [this, linSum_one, Int.min_eq_left (by omega)]

lemma curMin_step_minimal (nums : Array Int) (i : Nat) (curMin : Int)
    (h_min : ∀ start < i, curMin ≤ linSum nums start (i - start)) :
    ∀ start < i + 1, min nums[i]! (curMin + nums[i]!) ≤ linSum nums start (i + 1 - start) := by
  intro start hs
  by_cases heq : start = i
  · have hlen : i + 1 - start = 1 := by omega
    rw [hlen, linSum_one, heq]
    exact Int.min_le_left _ _
  · have hlt : start < i := by omega
    have hsub : i + 1 - start = (i - start) + 1 := by omega
    have hidx : start + (i - start) = i := by omega
    rw [hsub, linSum_succ, hidx]
    have hle : curMin + nums[i]! ≤ linSum nums start (i - start) + nums[i]! :=
      Int.add_le_add_right (h_min start hlt) _
    exact Int.le_trans (Int.min_le_right _ _) hle

lemma maxSum_step_achievable (nums : Array Int) (i : Nat) (maxSum curMax' : Int)
    (h_max_ach : ∃ start < i, ∃ len, 1 ≤ len ∧ start + len ≤ i ∧ linSum nums start len = maxSum)
    (h_cur_ach : ∃ start < i + 1, linSum nums start (i + 1 - start) = curMax') :
    ∃ start < i + 1, ∃ len, 1 ≤ len ∧ start + len ≤ i + 1 ∧ linSum nums start len = max maxSum curMax' := by
  by_cases h : curMax' ≤ maxSum
  · obtain ⟨start, hs, len, hlen, hlen_le, hsum⟩ := h_max_ach
    refine ⟨start, by omega, len, hlen, by omega, ?_⟩
    rw [hsum, Int.max_eq_left h]
  · obtain ⟨start, hs, hsum⟩ := h_cur_ach
    refine ⟨start, hs, i + 1 - start, by omega, by omega, ?_⟩
    rw [hsum, Int.max_eq_right (by omega)]

lemma maxSum_step_maximal (nums : Array Int) (i : Nat) (maxSum curMax' : Int)
    (h_max_max : ∀ start < i, ∀ len, 1 ≤ len → start + len ≤ i → linSum nums start len ≤ maxSum)
    (h_cur_max : ∀ start < i + 1, linSum nums start (i + 1 - start) ≤ curMax') :
    ∀ start < i + 1, ∀ len, 1 ≤ len → start + len ≤ i + 1 → linSum nums start len ≤ max maxSum curMax' := by
  intro start hs len hlen hlen_le
  by_cases hle : start + len ≤ i
  · have hs_lt : start < i := by omega
    exact Int.le_trans (h_max_max start hs_lt len hlen hle) (Int.le_max_left _ _)
  · have heq : start + len = i + 1 := by omega
    have hlen_eq : len = i + 1 - start := by omega
    subst hlen_eq
    exact Int.le_trans (h_cur_max start hs) (Int.le_max_right _ _)

lemma minSum_step_achievable (nums : Array Int) (i : Nat) (minSum curMin' : Int)
    (h_min_ach : ∃ start < i, ∃ len, 1 ≤ len ∧ start + len ≤ i ∧ linSum nums start len = minSum)
    (h_cur_ach : ∃ start < i + 1, linSum nums start (i + 1 - start) = curMin') :
    ∃ start < i + 1, ∃ len, 1 ≤ len ∧ start + len ≤ i + 1 ∧ linSum nums start len = min minSum curMin' := by
  by_cases h : minSum ≤ curMin'
  · obtain ⟨start, hs, len, hlen, hlen_le, hsum⟩ := h_min_ach
    refine ⟨start, by omega, len, hlen, by omega, ?_⟩
    rw [hsum, Int.min_eq_left h]
  · obtain ⟨start, hs, hsum⟩ := h_cur_ach
    refine ⟨start, hs, i + 1 - start, by omega, by omega, ?_⟩
    rw [hsum, Int.min_eq_right (by omega)]

lemma minSum_step_minimal (nums : Array Int) (i : Nat) (minSum curMin' : Int)
    (h_min_min : ∀ start < i, ∀ len, 1 ≤ len → start + len ≤ i → minSum ≤ linSum nums start len)
    (h_cur_min : ∀ start < i + 1, curMin' ≤ linSum nums start (i + 1 - start)) :
    ∀ start < i + 1, ∀ len, 1 ≤ len → start + len ≤ i + 1 → min minSum curMin' ≤ linSum nums start len := by
  intro start hs len hlen hlen_le
  by_cases hle : start + len ≤ i
  · have hs_lt : start < i := by omega
    exact Int.le_trans (Int.min_le_left _ _) (h_min_min start hs_lt len hlen hle)
  · have heq : start + len = i + 1 := by omega
    have hlen_eq : len = i + 1 - start := by omega
    subst hlen_eq
    exact Int.le_trans (Int.min_le_right _ _) (h_cur_min start hs)

lemma postcondition_all_neg (nums : Array Int) (maxSum : Int)
    (h_sz : nums.size > 0)
    (h_max_ach : ∃ start < nums.size, ∃ len, 1 ≤ len ∧ start + len ≤ nums.size ∧ linSum nums start len = maxSum)
    (h_max_max : ∀ start < nums.size, ∀ len, 1 ≤ len → start + len ≤ nums.size → linSum nums start len ≤ maxSum)
    (h_all_neg : maxSum < 0) :
    postcondition nums maxSum := by
  unfold postcondition isValidCircSegment
  constructor
  · obtain ⟨start, hs, len, hlen, hlen_le, hsum⟩ := h_max_ach
    refine ⟨start, len, ⟨h_sz, hs, hlen, by omega⟩, ?_⟩
    rw [circSegmentSum_non_wrap _ _ _ hlen_le, hsum]
  · intro start len h_valid
    by_cases h_wrap : start + len ≤ nums.size
    · rw [circSegmentSum_non_wrap _ _ _ h_wrap]
      exact h_max_max start h_valid.2.1 len h_valid.2.2.1 h_wrap
    · have h_all_le_max : ∀ j < nums.size, nums[j]! ≤ maxSum := by
        intro j hj
        have h1 : 1 ≤ 1 := by omega
        have h2 : j + 1 ≤ nums.size := by omega
        have := h_max_max j hj 1 h1 h2
        rwa [linSum_one] at this
      have h_sum_le : circSegmentSum nums start len ≤ (len : Int) * maxSum := by
        unfold circSegmentSum
        have h_le : (∑ i ∈ Finset.range len, nums[(start + i) % nums.size]!) ≤
            (∑ _i ∈ Finset.range len, maxSum) := by
          apply Finset.sum_le_sum
          intro k _hk
          exact h_all_le_max _ (Nat.mod_lt _ h_sz)
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range] at h_le
        exact h_le
      have h_len_ge1 : (1 : Int) ≤ (len : Int) := by omega
      have h_mul_le : (len : Int) * maxSum ≤ maxSum := by
        nlinarith
      exact le_trans h_sum_le h_mul_le

lemma postcondition_wrap (nums : Array Int) (total maxSum minSum : Int)
    (h_sz : nums.size > 0)
    (h_tot : total = prefixSum nums nums.size)
    (h_max_max : ∀ start < nums.size, ∀ len, 1 ≤ len → start + len ≤ nums.size → linSum nums start len ≤ maxSum)
    (h_min_ach : ∃ start < nums.size, ∃ len, 1 ≤ len ∧ start + len ≤ nums.size ∧ linSum nums start len = minSum)
    (h_min_min : ∀ start < nums.size, ∀ len, 1 ≤ len → start + len ≤ nums.size → minSum ≤ linSum nums start len)
    (h_nonneg : 0 ≤ maxSum)
    (h_wrap_better : maxSum < total - minSum) :
    postcondition nums (total - minSum) := by
  constructor
  · obtain ⟨start, _hstart, x, _hx₁, hx₂, hx₃⟩ := h_min_ach
    refine ⟨(start + x) % nums.size, nums.size - x, ?_, ?_⟩
    · refine ⟨h_sz, Nat.mod_lt _ h_sz, ?_, by omega⟩
      by_contra hc
      have hx_eq : x = nums.size := by omega
      have hstart_eq : start = 0 := by omega
      have hmin_eq_tot : minSum = total := by
        have : linSum nums 0 nums.size = prefixSum nums nums.size := by
          exact (prefixSum_eq_linSum_zero nums nums.size).symm
        rw [← hx₃, hstart_eq, hx_eq, this, ← h_tot]
      linarith
    · unfold circSegmentSum
      have h_complement_sum : ∑ k ∈ Finset.range (nums.size - x), nums[(start + x + k) % nums.size]! =
          ∑ k ∈ Finset.range nums.size, nums[k]! - ∑ k ∈ Finset.range x, nums[start + k]! := by
        have h_complement_sum : ∑ k ∈ Finset.range (nums.size - x), nums[(start + x + k) % nums.size]! =
            ∑ k ∈ Finset.range nums.size, nums[k]! - ∑ k ∈ Finset.range x, nums[(start + k) % nums.size]! := by
          have h_complement_sum : ∑ k ∈ Finset.range nums.size, nums[(start + k) % nums.size]! =
              ∑ k ∈ Finset.range x, nums[(start + k) % nums.size]! +
              ∑ k ∈ Finset.range (nums.size - x), nums[(start + x + k) % nums.size]! := by
            rw [← Finset.sum_range_add_sum_Ico _ (show x ≤ nums.size from by omega)]
            simp +decide [add_assoc, Finset.sum_Ico_eq_sum_range]
          rw [show ∑ k ∈ Finset.range nums.size, nums[(start + k) % nums.size]! =
              ∑ k ∈ Finset.range nums.size, nums[k]! from ?_] at h_complement_sum
          · linarith [h_complement_sum]
          have h_complement_sum : Finset.image (fun k => (start + k) % nums.size) (Finset.range nums.size) =
              Finset.range nums.size := by
            refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun k _hk =>
                Finset.mem_range.mpr (Nat.mod_lt _ h_sz)) ?_
            rw [Finset.card_image_of_injOn]
            intro a ha b hb hab
            simp_all +decide
            exact Nat.mod_eq_of_lt ha ▸ Nat.mod_eq_of_lt hb ▸ by simpa [← ZMod.natCast_eq_natCast_iff'] using hab
          generalize_proofs at *
          conv_rhs => rw [← h_complement_sum, Finset.sum_image (Finset.card_image_iff.mp (by aesop))]
        convert h_complement_sum using 2
        exact Finset.sum_congr rfl (fun k hk => by rw [Nat.mod_eq_of_lt (by linarith [Finset.mem_range.mp hk])])
      have h_mod_congr : ∑ i ∈ Finset.range (nums.size - x), nums[((start + x) % nums.size + i) % nums.size]! =
          ∑ k ∈ Finset.range (nums.size - x), nums[(start + x + k) % nums.size]! := by
        refine Finset.sum_congr rfl (fun k _hk => ?_)
        congr 1
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have h_tot_def : total = ∑ k ∈ Finset.range nums.size, nums[k]! := by
        rw [h_tot]; unfold prefixSum; rfl
      unfold linSum at hx₃
      rw [h_mod_congr, h_complement_sum, hx₃, h_tot_def]
  · intro start len h_valid
    rcases h_valid with ⟨h1, h2, h3, h4⟩
    cases lt_or_ge (start + len) nums.size with
    | inl h5 =>
      have : circSegmentSum nums start len = linSum nums start len :=
        circSegmentSum_non_wrap nums start len (by omega)
      rw [this]
      have : linSum nums start len ≤ maxSum := h_max_max start h2 len h3 (by omega)
      linarith
    | inr h5 =>
      have h_tot_le_max : total ≤ maxSum := by
        have h_lin : linSum nums 0 nums.size ≤ maxSum := h_max_max 0 h_sz nums.size (by omega) (by omega)
        have h_tot_eq : linSum nums 0 nums.size = total := by
          rw [← prefixSum_eq_linSum_zero, ← h_tot]
        rwa [h_tot_eq] at h_lin
      have h_segment_sum : circSegmentSum nums start len = total - ∑ j ∈ Finset.range (nums.size - len), nums[(start + len + j) % nums.size]! := by
        unfold circSegmentSum
        have h_sum_total : ∑ i ∈ Finset.range nums.size, nums[(start + i) % nums.size]! = ∑ j ∈ Finset.range nums.size, nums[j]! := by
          have h_img : Finset.image (fun i => (start + i) % nums.size) (Finset.range nums.size) = Finset.range nums.size := by
            refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun i _hi => Finset.mem_range.mpr (Nat.mod_lt _ h1)) ?_
            rw [Finset.card_image_of_injOn]
            intro i hi j hj hij
            simp_all +decide
            exact Nat.mod_eq_of_lt hi ▸ Nat.mod_eq_of_lt hj ▸ by simpa [← ZMod.natCast_eq_natCast_iff'] using hij
          conv_rhs => rw [← h_img, Finset.sum_image (Finset.card_image_iff.mp (by aesop))]
        have h_split : ∑ i ∈ Finset.range nums.size, nums[(start + i) % nums.size]! =
            ∑ i ∈ Finset.range len, nums[(start + i) % nums.size]! +
            ∑ j ∈ Finset.range (nums.size - len), nums[(start + len + j) % nums.size]! := by
          rw [← Finset.sum_range_add_sum_Ico _ (show len ≤ nums.size from h4)]
          simp +decide [add_assoc, Finset.sum_Ico_eq_sum_range]
        rw [h_sum_total] at h_split
        have : total = ∑ j ∈ Finset.range nums.size, nums[j]! := by
          rw [h_tot]; unfold prefixSum; rfl
        linarith
      by_cases h6 : len = nums.size
      · subst h6
        rw [show nums.size - nums.size = 0 by omega] at h_segment_sum
        simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at h_segment_sum
        linarith
      · have h_mod : ∀ j < nums.size - len, (start + len + j) % nums.size = start + len - nums.size + j := by
          intro j _hj
          have : (start + len + j) % nums.size = ((start + len - nums.size + j) + nums.size) % nums.size := by
            congr 1; omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h_comp_sum : ∑ j ∈ Finset.range (nums.size - len), nums[(start + len + j) % nums.size]! =
            linSum nums (start + len - nums.size) (nums.size - len) := by
          unfold linSum
          exact Finset.sum_congr rfl (fun x hx => by rw [h_mod x (Finset.mem_range.mp hx)])
        have h_min_le : minSum ≤ linSum nums (start + len - nums.size) (nums.size - len) :=
          h_min_min (start + len - nums.size) (by omega) (nums.size - len) (by omega) (by omega)
        linarith

lemma postcondition_nonwrap (nums : Array Int) (total maxSum minSum : Int)
    (h_sz : nums.size > 0)
    (h_tot : total = prefixSum nums nums.size)
    (h_max_ach : ∃ start < nums.size, ∃ len, 1 ≤ len ∧ start + len ≤ nums.size ∧ linSum nums start len = maxSum)
    (h_max_max : ∀ start < nums.size, ∀ len, 1 ≤ len → start + len ≤ nums.size → linSum nums start len ≤ maxSum)
    (h_min_min : ∀ start < nums.size, ∀ len, 1 ≤ len → start + len ≤ nums.size → minSum ≤ linSum nums start len)
    (h_nonwrap_better : total - minSum ≤ maxSum) :
    postcondition nums maxSum := by
  constructor
  · obtain ⟨start, hs, len, hlen, hlen_le, hsum⟩ := h_max_ach
    refine ⟨start, len, ⟨h_sz, hs, hlen, by omega⟩, ?_⟩
    rw [circSegmentSum_non_wrap _ _ _ hlen_le, hsum]
  · intro start len h_valid
    rcases h_valid with ⟨h1, h2, h3, h4⟩
    cases lt_or_ge (start + len) nums.size with
    | inl h5 =>
      have : circSegmentSum nums start len = linSum nums start len :=
        circSegmentSum_non_wrap nums start len (by omega)
      rw [this]
      exact h_max_max start h2 len h3 (by omega)
    | inr h5 =>
      have h_segment_sum : circSegmentSum nums start len = total - ∑ j ∈ Finset.range (nums.size - len), nums[(start + len + j) % nums.size]! := by
        unfold circSegmentSum
        have h_sum_total : ∑ i ∈ Finset.range nums.size, nums[(start + i) % nums.size]! = ∑ j ∈ Finset.range nums.size, nums[j]! := by
          have h_img : Finset.image (fun i => (start + i) % nums.size) (Finset.range nums.size) = Finset.range nums.size := by
            refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun i _hi => Finset.mem_range.mpr (Nat.mod_lt _ h1)) ?_
            rw [Finset.card_image_of_injOn]
            intro i hi j hj hij
            simp_all +decide
            exact Nat.mod_eq_of_lt hi ▸ Nat.mod_eq_of_lt hj ▸ by simpa [← ZMod.natCast_eq_natCast_iff'] using hij
          conv_rhs => rw [← h_img, Finset.sum_image (Finset.card_image_iff.mp (by aesop))]
        have h_split : ∑ i ∈ Finset.range nums.size, nums[(start + i) % nums.size]! =
            ∑ i ∈ Finset.range len, nums[(start + i) % nums.size]! +
            ∑ j ∈ Finset.range (nums.size - len), nums[(start + len + j) % nums.size]! := by
          rw [← Finset.sum_range_add_sum_Ico _ (show len ≤ nums.size from h4)]
          simp +decide [add_assoc, Finset.sum_Ico_eq_sum_range]
        rw [h_sum_total] at h_split
        have : total = ∑ j ∈ Finset.range nums.size, nums[j]! := by
          rw [h_tot]; unfold prefixSum; rfl
        linarith
      by_cases h6 : len = nums.size
      · subst h6
        rw [show nums.size - nums.size = 0 by omega] at h_segment_sum
        simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at h_segment_sum
        have h_lin : linSum nums 0 nums.size ≤ maxSum := h_max_max 0 h_sz nums.size (by omega) (by omega)
        have h_tot_eq : linSum nums 0 nums.size = total := by
          rw [← prefixSum_eq_linSum_zero, ← h_tot]
        linarith
      · have h_mod : ∀ j < nums.size - len, (start + len + j) % nums.size = start + len - nums.size + j := by
          intro j _hj
          have : (start + len + j) % nums.size = ((start + len - nums.size + j) + nums.size) % nums.size := by
            congr 1; omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h_comp_sum : ∑ j ∈ Finset.range (nums.size - len), nums[(start + len + j) % nums.size]! =
            linSum nums (start + len - nums.size) (nums.size - len) := by
          unfold linSum
          exact Finset.sum_congr rfl (fun x hx => by rw [h_mod x (Finset.mem_range.mp hx)])
        have h_min_le : minSum ≤ linSum nums (start + len - nums.size) (nums.size - len) :=
          h_min_min (start + len - nums.size) (by omega) (nums.size - len) (by omega) (by omega)
        linarith

lemma postcondition_nonneg (nums : Array Int) (total maxSum minSum : Int)
    (h_sz : nums.size > 0)
    (h_tot : total = prefixSum nums nums.size)
    (h_max_ach : ∃ start < nums.size, ∃ len, 1 ≤ len ∧ start + len ≤ nums.size ∧ linSum nums start len = maxSum)
    (h_max_max : ∀ start < nums.size, ∀ len, 1 ≤ len → start + len ≤ nums.size → linSum nums start len ≤ maxSum)
    (h_min_ach : ∃ start < nums.size, ∃ len, 1 ≤ len ∧ start + len ≤ nums.size ∧ linSum nums start len = minSum)
    (h_min_min : ∀ start < nums.size, ∀ len, 1 ≤ len → start + len ≤ nums.size → minSum ≤ linSum nums start len)
    (h_nonneg : 0 ≤ maxSum) :
    postcondition nums (max maxSum (total - minSum)) := by
  by_cases h : maxSum < total - minSum
  · rw [Int.max_eq_right (by omega)]
    exact postcondition_wrap nums total maxSum minSum h_sz h_tot h_max_max h_min_ach h_min_min h_nonneg h
  · rw [Int.max_eq_left (by omega)]
    exact postcondition_nonwrap nums total maxSum minSum h_sz h_tot h_max_ach h_max_max h_min_min (by omega)

prove_correct maxSumCircularSubarray by
  velvet_vcgen [maxSumCircularSubarray]
  · -- [1/34] index_bounds init
    unfold precondition at nonempty
    omega
  · -- [2/34] total_val init
    simp
  · -- [3/34] curMax_achievable init
    refine ⟨0, by omega, ?_⟩
    simp
  · -- [4/34] curMax_maximal init
    intro start hs
    have : start = 0 := by omega
    subst this
    simp
  · -- [5/34] maxSum_achievable init
    refine ⟨0, by omega, 1, by omega, by omega, ?_⟩
    simp
  · -- [6/34] maxSum_maximal init
    intro start hs len hlen hlen_le
    have : start = 0 ∧ len = 1 := by omega
    rcases this with ⟨rfl, rfl⟩
    simp
  · -- [7/34] curMin_achievable init
    refine ⟨0, by omega, ?_⟩
    simp
  · -- [8/34] curMin_minimal init
    intro start hs
    have : start = 0 := by omega
    subst this
    simp
  · -- [9/34] minSum_achievable init
    refine ⟨0, by omega, 1, by omega, by omega, ?_⟩
    simp
  · -- [10/34] minSum_minimal init
    intro start hs len hlen hlen_le
    have : start = 0 ∧ len = 1 := by omega
    rcases this with ⟨rfl, rfl⟩
    simp
  · -- [11/34] maximum (all_neg)
    rename_i nums
    subst done
    exact postcondition_all_neg nums maxSum nonempty maxSum_achievable maxSum_maximal all_neg
  · -- [12/34] maximum (¬ all_neg)
    rename_i nums
    have h_ge : 0 ≤ maxSum := by omega
    subst done
    exact postcondition_nonneg nums total maxSum minSum nonempty total_val maxSum_achievable maxSum_maximal minSum_achievable minSum_minimal h_ge
  · -- [13/34] remaining step
    omega
  · -- [14/34] index_bounds step
    omega
  · -- [15/34] total_val step
    rw [total_val, prefixSum_succ]
  · -- [16/34] curMax_achievable step
    exact curMax_step_achievable _ _ _ curMax_achievable
  · -- [17/34] curMax_maximal step
    exact curMax_step_maximal _ _ _ curMax_maximal
  · -- [18/34] maxSum_achievable step
    have h_cur := curMax_step_achievable _ _ _ curMax_achievable
    exact maxSum_step_achievable _ _ _ _ maxSum_achievable h_cur
  · -- [19/34] maxSum_maximal step
    have h_cur := curMax_step_maximal _ _ _ curMax_maximal
    exact maxSum_step_maximal _ _ _ _ maxSum_maximal h_cur
  · -- [20/34] curMin_achievable step
    exact curMin_step_achievable _ _ _ curMin_achievable
  · -- [21/34] curMin_minimal step
    exact curMin_step_minimal _ _ _ curMin_minimal
  · -- [22/34] minSum_achievable step
    have h_cur := curMin_step_achievable _ _ _ curMin_achievable
    exact minSum_step_achievable _ _ _ _ minSum_achievable h_cur
  · -- [23/34] minSum_minimal step
    have h_cur := curMin_step_minimal _ _ _ curMin_minimal
    exact minSum_step_minimal _ _ _ _ minSum_minimal h_cur
  · -- [24/34] index_bounds exit
    assumption
  · -- [25/34] total_val exit
    assumption
  · -- [26/34] curMax_achievable exit
    assumption
  · -- [27/34] curMax_maximal exit
    assumption
  · -- [28/34] maxSum_achievable exit
    assumption
  · -- [29/34] maxSum_maximal exit
    assumption
  · -- [30/34] curMin_achievable exit
    assumption
  · -- [31/34] curMin_minimal exit
    assumption
  · -- [32/34] minSum_achievable exit
    assumption
  · -- [33/34] minSum_minimal exit
    assumption
  · -- [34/34] done exit
    omega

end Proof

end MaximumSumCircularSubarray
