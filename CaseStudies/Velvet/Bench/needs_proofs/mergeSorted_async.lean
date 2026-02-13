import CaseStudies.Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- mergeSorted: Merge two sorted arrays of natural numbers into a single sorted array
-- **IMPORTANT: complexity should be O(n)**
-- Natural language breakdown:
-- 1. We have two input arrays a1 and a2, both containing natural numbers
-- 2. Both input arrays must be sorted in non-decreasing order (precondition)
-- 3. The output array must contain all elements from both input arrays
-- 4. Each element appears exactly as many times as it appears in a1 plus a2 combined
-- 5. The output array must also be sorted in non-decreasing order
-- 6. The size of the output equals the sum of sizes of the two input arrays
-- 7. This is a merge operation that preserves all elements (including duplicates)

@[grind]
def isSorted (arr : Array Nat) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

lemma isSorted_le (arr : Array Nat) (i : Nat) :
  isSorted arr → i + 1 < arr.size → arr[i]! ≤ arr[i + 1]! := by
  intro s; apply s; grind

section Impl
method mergeSorted (a1 : Array Nat) (a2 : Array Nat)
  return (result : Array Nat)
  require isSorted a1
  require isSorted a2
  ensures result.size = a1.size + a2.size
  ensures isSorted result
  ensures ∀ v : Nat, result.count v = a1.count v + a2.count v
  do
  let mut result : Array Nat := #[]
  let mut i : Nat := 0
  let mut j : Nat := 0

  while i < a1.size ∨ j < a2.size
    -- Invariant 1: Index bounds
    -- Init: i=0, j=0, both ≤ respective sizes
    -- Pres: increments stay within bounds due to loop condition checks
    invariant "i_bound" i ≤ a1.size
    invariant "j_bound" j ≤ a2.size
    -- Invariant 2: Result size tracks progress
    -- Init: result.size = 0 = 0 + 0 = i + j
    -- Pres: each iteration pushes one element and increments one index
    invariant "size_inv" result.size = i + j
    -- Invariant 3: Result array is sorted
    -- Init: empty array is sorted
    -- Pres: we always push element ≤ all remaining, maintaining sortedness
    invariant "sorted_inv" isSorted result
    -- Invariant 4: Count preservation for elements processed so far
    -- Init: all counts are 0
    -- Pres: pushing from a1[i] or a2[j] updates counts correctly
    invariant "count_inv" ∀ v : Nat, result.count v = (a1.take i).count v + (a2.take j).count v
    -- Invariant 5: Last element of result is ≤ remaining elements in a1
    -- This ensures we can extend result with a1[i..] maintaining sortedness
    invariant "last_le_a1" result.size > 0 → i < a1.size → result[result.size - 1]! ≤ a1[i]!
    -- Invariant 6: Last element of result is ≤ remaining elements in a2
    invariant "last_le_a2" result.size > 0 → j < a2.size → result[result.size - 1]! ≤ a2[j]!
    done_with i >= a1.size ∧ j >= a2.size
  do
    if i >= a1.size then
      -- a1 exhausted, take from a2
      result := result.push a2[j]!
      j := j + 1
    else
      if j >= a2.size then
        -- a2 exhausted, take from a1
        result := result.push a1[i]!
        i := i + 1
      else
        -- Both have elements, take smaller
        if a1[i]! <= a2[j]! then
          result := result.push a1[i]!
          i := i + 1
        else
          result := result.push a2[j]!
          j := j + 1

  return result
end Impl

section Proof
set_option maxHeartbeats 1000000

@[grind]
theorem count_take [DecidableEq α] [Inhabited α] {a : α} {xs : Array α} :
  n < xs.size →
  (xs.take (n + 1)).count a = if xs[n]! = a then (xs.take n).count a + 1 else (xs.take n).count a := by
  intro; grind [Array.extract_succ_right]

lemma mergeSorted_correct (a1 : Array Nat) (a2 : Array Nat) :
    triple
      (with_name_prefix`require isSorted a2 ∧ with_name_prefix`require isSorted a1)
      (mergeSorted a1 a2)
      (fun result =>
        (with_name_prefix`ensures∀ v : Nat, result.count v = a1.count v + a2.count v) ∧
          (with_name_prefix`ensures isSorted result) ∧
            with_name_prefix`ensures result.size = a1.size + a2.size) :=
  by
  unfold mergeSorted
  loom_solve_async <;> ((try simp); grind [isSorted_le, Array.take_size])



end Proof
