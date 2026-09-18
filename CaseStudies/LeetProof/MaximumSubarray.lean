module

public import Velvet
public meta import Velvet

/-!
## Program description

Return the maximum sum of a nonempty contiguous subarray of a nonempty integer
array. The implementation is Kadane's algorithm with an index scan and does not
materialize a tail array. The program is expected to run in O(n) time and O(1)
extra space.
-/

namespace MaximumSubarray

section Specs

public def arraySum (arr : Array Int) : Int :=
  arr.foldl (fun acc x => acc + x) 0

public def rangeSum (nums : Array Int) (start stop : Nat) : Int :=
  arraySum (nums.extract start stop)

public def precondition (nums : Array Int) : Prop := nums.size > 0

public def postcondition (nums : Array Int) (result : Int) : Prop :=
  (∃ start stop, start < stop ∧ stop ≤ nums.size ∧
    rangeSum nums start stop = result) ∧
  (∀ start stop, start < stop ∧ stop ≤ nums.size →
    rangeSum nums start stop ≤ result)

end Specs

section Implementation

method maximumSubarray (nums : Array Int)
  returns (result : Int)
  requires nonempty: precondition nums
  ensures maximum: postcondition nums result
do
  let mut i : Nat := 1
  let mut current : Int := nums[0]!
  let mut best : Int := nums[0]!
  while' scanning: i < nums.size
    invariant index_bounds: 1 ≤ i ∧ i ≤ nums.size
    invariant current_achievable:
      ∃ start, start < i ∧ rangeSum nums start i = current
    invariant current_maximal:
      ∀ start, start < i → rangeSum nums start i ≤ current
    invariant best_achievable:
      ∃ start stop, start < stop ∧ stop ≤ i ∧ rangeSum nums start stop = best
    invariant best_maximal:
      ∀ start stop, start < stop → stop ≤ i → rangeSum nums start stop ≤ best
    decreasing remaining: nums.size - i
    done_with complete: i = nums.size
  do
    let x := nums[i]!
    current := max x (current + x)
    best := max best current
    i := i + 1
  return best

end Implementation

section Proof

theorem rangeSum_toList (nums : Array Int) (start stop : Nat) :
    rangeSum nums start stop =
      (nums.toList.extract start stop).foldl (fun acc x => acc + x) 0 := by
  unfold rangeSum arraySum
  calc
    (nums.extract start stop).foldl (fun acc x => acc + x) 0 =
        (nums.extract start stop).toList.foldl (fun acc x => acc + x) 0 := by
      simpa using (Array.foldl_toList (xs := nums.extract start stop)
        (f := fun acc x => acc + x) (init := (0 : Int))).symm
    _ = _ := by simp [Array.toList_extract]

@[simp] theorem rangeSum_single (nums : Array Int) (i : Nat) :
    rangeSum nums i (i + 1) = nums[i]! := by
  by_cases h : i < nums.size
  · rw [rangeSum_toList]
    simp [List.extract, List.take_add_one, List.getElem?_drop, h]
  · have hsize : nums.size ≤ i := by omega
    rw [rangeSum_toList]
    simp [List.extract, List.take_add_one, h, hsize]

theorem rangeSum_succ (nums : Array Int) (start i : Nat) (h : start ≤ i) :
    rangeSum nums start (i + 1) = rangeSum nums start i + nums[i]! := by
  by_cases hi : i < nums.size
  · rw [rangeSum_toList, rangeSum_toList]
    have hsub : i + 1 - start = (i - start) + 1 := by omega
    rw [show nums.toList.extract start (i + 1) =
        List.take ((i - start) + 1) (List.drop start nums.toList) by
          simp [List.extract, hsub]]
    rw [List.take_add_one, List.foldl_append]
    simp [List.extract, List.getElem?_drop, hi, h]
  · have hsize : nums.size ≤ i := by omega
    rw [rangeSum_toList, rangeSum_toList]
    have hsame : nums.toList.extract start (i + 1) = nums.toList.extract start i := by
      unfold List.extract
      rw [List.take_of_length_le, List.take_of_length_le]
      · simp; omega
      · simp; omega
    rw [hsame]
    simp [getElem!_neg, hi]

prove_correct maximumSubarray by
  velvet_vcgen [maximumSubarray, precondition, postcondition] with try finish
  case index_bounds =>
    unfold precondition at nonempty
    omega
  case current_achievable =>
    exact ⟨0, by omega, rangeSum_single _ 0⟩
  case current_maximal =>
    intro start hs
    have : start = 0 := by omega
    subst start
    simp [rangeSum_single]
  case best_achievable =>
    exact ⟨0, 1, by omega, by omega, rangeSum_single _ 0⟩
  case best_maximal =>
    intro start stop hs hstop
    have hstart : start = 0 := by omega
    have hstop' : stop = 1 := by omega
    subst start
    subst stop
    simp [rangeSum_single]
  case maximum =>
    subst i
    refine ⟨best_achievable, ?_⟩
    intro start stop h
    exact best_maximal start stop h.1 h.2
  case current_achievable =>
    rename_i nums
    by_cases hchoose : nums[i]! ≤ current + nums[i]!
    · obtain ⟨start, hs, hsum⟩ := current_achievable
      refine ⟨start, by omega, ?_⟩
      rw [rangeSum_succ _ _ _ (by omega), hsum, Int.max_eq_right hchoose]
    · refine ⟨i, by omega, ?_⟩
      rw [rangeSum_single, Int.max_eq_left (by omega)]
  case current_maximal =>
    rename_i nums
    intro start hs
    by_cases heq : start = i
    · subst start
      rw [rangeSum_single]
      exact Int.le_max_left _ _
    · have hlt : start < i := by omega
      rw [rangeSum_succ _ _ _ (by omega)]
      exact Int.le_trans (Int.add_le_add_right (current_maximal start hlt) _)
        (Int.le_max_right _ _)
  case best_achievable =>
    rename_i nums
    let next := max nums[i]! (current + nums[i]!)
    by_cases hbest : next ≤ best
    · obtain ⟨start, stop, hs, hstop, hsum⟩ := best_achievable
      refine ⟨start, stop, hs, by omega, ?_⟩
      simpa [next, Int.max_eq_left hbest] using hsum
    · by_cases hchoose : nums[i]! ≤ current + nums[i]!
      · obtain ⟨start, hs, hsum⟩ := current_achievable
        refine ⟨start, i + 1, by omega, by omega, ?_⟩
        have hnext : next = current + nums[i]! := Int.max_eq_right hchoose
        have houter : max best next = next := Int.max_eq_right (by omega)
        rw [rangeSum_succ _ _ _ (by omega), hsum, houter, hnext]
      · refine ⟨i, i + 1, by omega, by omega, ?_⟩
        have hnext : next = nums[i]! := Int.max_eq_left (by omega)
        have houter : max best next = next := Int.max_eq_right (by omega)
        rw [rangeSum_single, houter, hnext]
  case best_maximal =>
    rename_i nums
    intro start stop hs hstop
    by_cases hold : stop ≤ i
    · exact Int.le_trans (best_maximal start stop hs hold) (Int.le_max_left _ _)
    · have hstop_eq : stop = i + 1 := by omega
      subst stop
      by_cases heq : start = i
      · subst start
        rw [rangeSum_single]
        exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _)
      · have hlt : start < i := by omega
        rw [rangeSum_succ _ _ _ (by omega)]
        apply Int.le_trans (Int.add_le_add_right (current_maximal start hlt) _)
        exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _)

end Proof

end MaximumSubarray
