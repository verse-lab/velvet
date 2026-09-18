module

public import Velvet
public meta import Velvet

/-!
## Program description

Given an integer array `arr`, remove a contiguous subarray (possibly empty) so
that the remaining elements are non-decreasing, and return the minimum removed length.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace ShortestSubarrayToBeRemovedToMakeArraySorted

section Specs

public def isNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < arr.size → arr[i]! ≤ arr[i + 1]!

public def removeSubarray (arr : Array Int) (l : Nat) (r : Nat) : Array Int :=
  arr.extract 0 l ++ arr.extract r arr.size

public def validRemoval (arr : Array Int) (l : Nat) (r : Nat) : Prop :=
  l ≤ r ∧ r ≤ arr.size ∧ isNondecreasing (removeSubarray arr l r)

public def precondition (_arr : Array Int) : Prop :=
  True

public def postcondition (arr : Array Int) (result : Nat) : Prop :=
  (∃ (l : Nat) (r : Nat), validRemoval arr l r ∧ result = r - l) ∧
  (∀ (l : Nat) (r : Nat), validRemoval arr l r → result ≤ r - l)

end Specs

section Implementation

method findLengthOfShortestSubarray (arr : Array Int)
  returns (result : Nat)
  requires valid_input: precondition arr
  ensures shortest_removal: postcondition arr result
do
  let n := arr.size
  if small: n ≤ 1 then
    return 0
  else
    let mut r : Nat := n - 1
    while find_suffix: r > 0 ∧ arr[r - 1]! ≤ arr[r]!
      invariant r_lt_n: r < n
      invariant suffix_sorted: ∀ (j : Nat), r ≤ j → j + 1 < n → arr[j]! ≤ arr[j + 1]!
      decreasing r_dec: r
      done_with suffix_done: r = 0 ∨ (r > 0 ∧ arr[r - 1]! > arr[r]!)
    do
      r := r - 1
    if already_sorted: r = 0 then
      return 0
    else
      let mut best : Nat := r
      let mut left : Nat := 0
      let mut right : Nat := r
      while outer: left < r ∧ (left = 0 ∨ arr[left - 1]! ≤ arr[left]!)
        invariant left_le_r: left ≤ r
        invariant right_range: r ≤ right ∧ right ≤ n
        invariant left_zero_right: left = 0 → right = r
        invariant best_le_n: best ≤ n
        invariant prefix_sorted: ∀ (i : Nat), i + 1 < left → arr[i]! ≤ arr[i + 1]!
        invariant best_achievable: ∃ (l' : Nat) (r' : Nat), validRemoval arr l' r' ∧ best = r' - l'
        invariant best_optimal: ∀ (l' : Nat) (r' : Nat), validRemoval arr l' r' → l' ≤ left → best ≤ r' - l'
        invariant right_monotone: ∀ (j : Nat), r ≤ j → j < right → left > 0 → arr[left - 1]! > arr[j]!
        decreasing rem_left: r - left
        done_with done_outer: left = r ∨ (left > 0 ∧ arr[left - 1]! > arr[left]!)
      do
        while inner: right < n ∧ arr[left]! > arr[right]!
          invariant inner_right_bounds: r ≤ right ∧ right ≤ n
          invariant inner_right_monotone: ∀ (j : Nat), r ≤ j → j < right → arr[left]! > arr[j]!
          decreasing rem_right: n - right
          done_with done_inner: right = n ∨ arr[left]! ≤ arr[right]!
        do
          right := right + 1
        let cand := right - (left + 1)
        if cand_better: cand < best then
          best := cand
        left := left + 1
      return best

end Implementation

section Proof

theorem removeSubarray_size (arr : Array Int) (l r : Nat) (hl : l ≤ r) (hr : r ≤ arr.size) :
    (removeSubarray arr l r).size = l + (arr.size - r) := by
  unfold removeSubarray
  simp
  omega

theorem removeSubarray_get_left (arr : Array Int) (l r k : Nat)
    (hl : l ≤ r) (hr : r ≤ arr.size) (hk : k < l) :
    (removeSubarray arr l r)[k]! = arr[k]! := by
  unfold removeSubarray
  have h1 : (arr.extract 0 l).size = l := by
    simp
    omega
  have hk_rem : k < (arr.extract 0 l ++ arr.extract r arr.size).size := by
    rw [Array.size_append, h1]
    omega
  rw [getElem!_pos _ k hk_rem]
  rw [Array.getElem_append_left (by rw [h1]; exact hk)]
  rw [getElem!_pos arr k (by omega)]
  rw [Array.getElem_extract]
  congr 1
  omega

theorem removeSubarray_get_right (arr : Array Int) (l r k : Nat)
    (hl : l ≤ r) (hr : r ≤ arr.size) (hkl : l ≤ k) (hk : k < l + (arr.size - r)) :
    (removeSubarray arr l r)[k]! = arr[r + (k - l)]! := by
  unfold removeSubarray
  have h1 : (arr.extract 0 l).size = l := by
    simp
    omega
  have h2 : (arr.extract r arr.size).size = arr.size - r := by
    simp
  have hk_rem : k < (arr.extract 0 l ++ arr.extract r arr.size).size := by
    rw [Array.size_append, h1, h2]
    exact hk
  rw [getElem!_pos _ k hk_rem]
  rw [Array.getElem_append_right (by rw [h1]; exact hkl)]
  have hk_arr : r + (k - l) < arr.size := by omega
  rw [getElem!_pos arr (r + (k - l)) hk_arr]
  rw [Array.getElem_extract]
  congr 1
  omega

theorem validRemoval_of_split (arr : Array Int) (l r : Nat)
    (hl : l ≤ r) (hr : r ≤ arr.size)
    (h_pref : ∀ i, i + 1 < l → arr[i]! ≤ arr[i + 1]!)
    (h_suff : ∀ j, r ≤ j → j + 1 < arr.size → arr[j]! ≤ arr[j + 1]!)
    (h_conn : 0 < l → r < arr.size → arr[l - 1]! ≤ arr[r]!) :
    validRemoval arr l r := by
  unfold validRemoval isNondecreasing
  refine ⟨hl, hr, ?_⟩
  intro k hk
  have hsz := removeSubarray_size arr l r hl hr
  rw [hsz] at hk
  by_cases hk_left : k + 1 < l
  · rw [removeSubarray_get_left arr l r k hl hr (by omega)]
    rw [removeSubarray_get_left arr l r (k + 1) hl hr hk_left]
    exact h_pref k hk_left
  · by_cases hk_mid : k + 1 = l
    · have hk_eq : k = l - 1 := by omega
      have hl_pos : 0 < l := by omega
      have hr_lt : r < arr.size := by omega
      rw [removeSubarray_get_left arr l r k hl hr (by omega)]
      have hkl : l ≤ k + 1 := by omega
      rw [removeSubarray_get_right arr l r (k + 1) hl hr hkl (by omega)]
      have : r + (k + 1 - l) = r := by omega
      rw [this, hk_eq]
      exact h_conn hl_pos hr_lt
    · have hkl : l ≤ k := by omega
      rw [removeSubarray_get_right arr l r k hl hr hkl (by omega)]
      rw [removeSubarray_get_right arr l r (k + 1) hl hr (by omega) (by omega)]
      have h_idx : r + (k + 1 - l) = (r + (k - l)) + 1 := by omega
      rw [h_idx]
      apply h_suff (r + (k - l)) (by omega)
      omega

theorem validRemoval_prefix_sorted (arr : Array Int) (l r : Nat)
    (hval : validRemoval arr l r) (i : Nat) (hi : i + 1 < l) :
    arr[i]! ≤ arr[i + 1]! := by
  unfold validRemoval isNondecreasing at hval
  obtain ⟨hl, hr, hnd⟩ := hval
  have hsz := removeSubarray_size arr l r hl hr
  have hk : i + 1 < (removeSubarray arr l r).size := by
    rw [hsz]
    omega
  have h_step := hnd i hk
  rw [removeSubarray_get_left arr l r i hl hr (by omega)] at h_step
  rw [removeSubarray_get_left arr l r (i + 1) hl hr hi] at h_step
  exact h_step

theorem validRemoval_suffix_sorted (arr : Array Int) (l r : Nat)
    (hval : validRemoval arr l r) (j : Nat) (hj : r ≤ j) (hj1 : j + 1 < arr.size) :
    arr[j]! ≤ arr[j + 1]! := by
  unfold validRemoval isNondecreasing at hval
  obtain ⟨hl, hr, hnd⟩ := hval
  have hsz := removeSubarray_size arr l r hl hr
  let k := l + (j - r)
  have hk : k + 1 < (removeSubarray arr l r).size := by
    rw [hsz]
    omega
  have h_step := hnd k hk
  have hkl : l ≤ k := by omega
  have hkl1 : l ≤ k + 1 := by omega
  rw [removeSubarray_get_right arr l r k hl hr hkl (by omega)] at h_step
  rw [removeSubarray_get_right arr l r (k + 1) hl hr hkl1 (by omega)] at h_step
  have heq1 : r + (k - l) = j := by omega
  have heq2 : r + (k + 1 - l) = j + 1 := by omega
  rw [heq1, heq2] at h_step
  exact h_step

theorem validRemoval_connect (arr : Array Int) (l r : Nat)
    (hval : validRemoval arr l r) (hl_pos : 0 < l) (hr_lt : r < arr.size) :
    arr[l - 1]! ≤ arr[r]! := by
  unfold validRemoval isNondecreasing at hval
  obtain ⟨hl, hr, hnd⟩ := hval
  have hsz := removeSubarray_size arr l r hl hr
  have hk : (l - 1) + 1 < (removeSubarray arr l r).size := by
    rw [hsz]
    omega
  have h_step := hnd (l - 1) hk
  rw [removeSubarray_get_left arr l r (l - 1) hl hr (by omega)] at h_step
  have hkl : l ≤ l - 1 + 1 := by omega
  rw [removeSubarray_get_right arr l r (l - 1 + 1) hl hr hkl (by omega)] at h_step
  have heq : r + (l - 1 + 1 - l) = r := by omega
  rw [heq] at h_step
  exact h_step

theorem suffix_lower_bound (arr : Array Int) (r l' r' : Nat)
    (hr_pos : 0 < r) (hr_lt : r < arr.size)
    (h_drop : arr[r]! < arr[r - 1]!)
    (hval : validRemoval arr l' r') :
    r ≤ r' := by
  by_cases h_le : r ≤ r'
  · exact h_le
  · have hr'_le : r' ≤ r - 1 := by omega
    have hr1 : r - 1 + 1 < arr.size := by omega
    have h_suff := validRemoval_suffix_sorted arr l' r' hval (r - 1) hr'_le hr1
    have : r - 1 + 1 = r := by omega
    rw [this] at h_suff
    omega

theorem prefix_upper_bound (arr : Array Int) (left l' r' : Nat)
    (hleft_pos : 0 < left)
    (h_drop : arr[left]! < arr[left - 1]!)
    (hval : validRemoval arr l' r') :
    l' ≤ left := by
  by_cases h_le : l' ≤ left
  · exact h_le
  · have hi : left - 1 + 1 < l' := by omega
    have h_pref := validRemoval_prefix_sorted arr l' r' hval (left - 1) hi
    have : left - 1 + 1 = left := by omega
    rw [this] at h_pref
    omega

prove_correct findLengthOfShortestSubarray by
  velvet_vcgen [findLengthOfShortestSubarray, postcondition] with try finish
  · -- Goal 1: small : arr✝.size ≤ 1
    rename_i arr
    unfold postcondition
    refine ⟨⟨0, 0, ?_, rfl⟩, fun _ _ _ => by omega⟩
    unfold validRemoval isNondecreasing
    refine ⟨by omega, by omega, fun i hi => ?_⟩
    have hsz := removeSubarray_size arr 0 0 (by omega) (by omega)
    rw [hsz] at hi
    omega
  · -- Goal 2: already_sorted : r = 0
    rename_i arr
    unfold postcondition
    refine ⟨⟨0, 0, ?_, rfl⟩, fun _ _ _ => by omega⟩
    apply validRemoval_of_split arr 0 0 (by omega) (by omega) (fun _ h => by omega)
    · intro j _ hj
      subst already_sorted
      exact suffix_sorted j (by omega) hj
    · intro h
      omega
  · -- Goal 3: best_achievable before outer loop
    rename_i arr
    refine ⟨0, r, ?_, by omega⟩
    apply validRemoval_of_split arr 0 r (by omega) (by omega) (fun _ h => by omega) suffix_sorted (fun h => by omega)
  · -- Goal 4: best_optimal before outer loop
    rename_i arr
    intro l' r' hval hl'
    have hl'_0 : l' = 0 := by omega
    subst hl'_0
    rcases suffix_done with hr0 | ⟨hr_pos, h_drop⟩
    · contradiction
    · have hr_le := suffix_lower_bound arr r 0 r' hr_pos r_lt_n h_drop hval
      omega
  · -- Goal 5: shortest_removal after outer loop
    rename_i arr
    unfold postcondition
    refine ⟨best_achievable, ?_⟩
    intro l' r' hval
    rcases done_outer with h_left_r | ⟨h_left_pos, h_drop⟩
    · subst h_left_r
      rcases suffix_done with hr0 | ⟨hr_pos, h_drop_r⟩
      · contradiction
      · have hl'_le := prefix_upper_bound arr left l' r' hr_pos h_drop_r hval
        exact best_optimal l' r' hval hl'_le
    · have hl'_le := prefix_upper_bound arr left l' r' h_left_pos h_drop hval
      exact best_optimal l' r' hval hl'_le
  · -- Goal 6: best_achievable after inner loop
    rename_i arr right_old
    refine ⟨left + 1, right, ?_, rfl⟩
    apply validRemoval_of_split arr (left + 1) right (by omega) inner_right_bounds.2
    · intro i hi
      by_cases hi_lt : i + 1 < left
      · exact prefix_sorted i hi_lt
      · have hi_eq : i = left - 1 := by omega
        subst hi_eq
        rcases outer.2 with h0 | h_step
        · have : left = 0 := h0; omega
        · have h_idx : left - 1 + 1 = left := by omega
          rw [h_idx]
          exact h_step
    · intro j hj hj1
      apply suffix_sorted j (by omega) hj1
    · intro _ _
      rcases done_inner with hr_eq | h_conn
      · omega
      · exact h_conn
  · -- Goal 7: best_optimal when cand < best
    rename_i arr right_old
    intro l' r' hval hl'
    by_cases hl_le : l' ≤ left
    · have h1 := best_optimal l' r' hval hl_le
      omega
    · have hl_eq : l' = left + 1 := by omega
      subst hl_eq
      rcases suffix_done with hr0 | ⟨hr_pos, h_drop⟩
      · contradiction
      · have hr_le := suffix_lower_bound arr r (left + 1) r' hr_pos r_lt_n h_drop hval
        by_cases hr'_lt : r' < right
        · have h_lt := inner_right_monotone r' hr_le hr'_lt
          have hr'_lt_n : r' < arr.size := by omega
          have h_conn := validRemoval_connect arr (left + 1) r' hval (by omega) hr'_lt_n
          have h_idx : (left + 1) - 1 = left := by omega
          rw [h_idx] at h_conn
          omega
        · omega
  · -- Goal 8: best_optimal when ¬ cand < best
    rename_i arr right_old
    intro l' r' hval hl'
    by_cases hl_le : l' ≤ left
    · exact best_optimal l' r' hval hl_le
    · have hl_eq : l' = left + 1 := by omega
      subst hl_eq
      rcases suffix_done with hr0 | ⟨hr_pos, h_drop⟩
      · contradiction
      · have hr_le := suffix_lower_bound arr r (left + 1) r' hr_pos r_lt_n h_drop hval
        by_cases hr'_lt : r' < right
        · have h_lt := inner_right_monotone r' hr_le hr'_lt
          have hr'_lt_n : r' < arr.size := by omega
          have h_conn := validRemoval_connect arr (left + 1) r' hval (by omega) hr'_lt_n
          have h_idx : (left + 1) - 1 = left := by omega
          rw [h_idx] at h_conn
          omega
        · omega

end Proof

end ShortestSubarrayToBeRemovedToMakeArraySorted
