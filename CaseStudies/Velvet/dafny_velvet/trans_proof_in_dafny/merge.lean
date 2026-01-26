import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

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

section Specs
-- Helper: check if an array is sorted in non-decreasing order
def isSortedArray (arr : Array Nat) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: count occurrences of a value in an array
def countInArray (arr : Array Nat) (v : Nat) : Nat :=
  arr.toList.count v

-- Precondition: both input arrays must be sorted
def precondition (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  isSortedArray a1 ∧ isSortedArray a2

-- Postcondition clauses
-- 1. The result size equals the sum of input sizes
def ensures1 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  result.size = a1.size + a2.size

-- 2. The result is sorted in non-decreasing order
def ensures2 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  isSortedArray result

-- 3. Every element's count in result equals its count in a1 plus its count in a2
def ensures3 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  ∀ v : Nat, countInArray result v = countInArray a1 v + countInArray a2 v

def postcondition (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  ensures1 a1 a2 result ∧
  ensures2 a1 a2 result ∧
  ensures3 a1 a2 result
end Specs

section Impl
method mergeSorted (a1 : Array Nat) (a2 : Array Nat)
  return (result : Array Nat)
  require precondition a1 a2
  ensures postcondition a1 a2 result
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
    invariant "sorted_inv" isSortedArray result
    -- Invariant 4: Count preservation for elements processed so far
    -- Init: all counts are 0
    -- Pres: pushing from a1[i] or a2[j] updates counts correctly
    invariant "count_inv" ∀ v : Nat, countInArray result v = countInArray (Array.mk (a1.toList.take i)) v + countInArray (Array.mk (a2.toList.take j)) v
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

section TestCases
-- Test case 1: Basic merge of two interleaved arrays (from problem)
def test1_a1 : Array Nat := #[1, 3, 5]
def test1_a2 : Array Nat := #[2, 4, 6]
def test1_Expected : Array Nat := #[1, 2, 3, 4, 5, 6]

-- Test case 2: First array empty
def test2_a1 : Array Nat := #[]
def test2_a2 : Array Nat := #[1, 2, 3]
def test2_Expected : Array Nat := #[1, 2, 3]

-- Test case 3: Second array empty
def test3_a1 : Array Nat := #[1, 2, 3]
def test3_a2 : Array Nat := #[]
def test3_Expected : Array Nat := #[1, 2, 3]

-- Test case 4: Both arrays empty
def test4_a1 : Array Nat := #[]
def test4_a2 : Array Nat := #[]
def test4_Expected : Array Nat := #[]

-- Test case 5: Arrays with duplicate elements
def test5_a1 : Array Nat := #[1, 1, 2]
def test5_a2 : Array Nat := #[1, 2, 2]
def test5_Expected : Array Nat := #[1, 1, 1, 2, 2, 2]

-- Test case 6: Arrays with interleaved ranges
def test6_a1 : Array Nat := #[10, 20, 30]
def test6_a2 : Array Nat := #[5, 15, 25]
def test6_Expected : Array Nat := #[5, 10, 15, 20, 25, 30]

-- Test case 7: Longer arrays with alternating elements
def test7_a1 : Array Nat := #[1, 3, 5, 7, 9]
def test7_a2 : Array Nat := #[2, 4, 6, 8, 10]
def test7_Expected : Array Nat := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

-- Test case 8: Arrays with all same elements
def test8_a1 : Array Nat := #[5, 5, 5]
def test8_a2 : Array Nat := #[5, 5, 5]
def test8_Expected : Array Nat := #[5, 5, 5, 5, 5, 5]

-- Test case 9: Single element arrays
def test9_a1 : Array Nat := #[1]
def test9_a2 : Array Nat := #[2]
def test9_Expected : Array Nat := #[1, 2]

-- Test case 10: One array completely before the other
def test10_a1 : Array Nat := #[1, 2, 3]
def test10_a2 : Array Nat := #[4, 5, 6]
def test10_Expected : Array Nat := #[1, 2, 3, 4, 5, 6]

-- Recommend to validate: 1, 5, 6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((mergeSorted test1_a1 test1_a2).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((mergeSorted test2_a1 test2_a2).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((mergeSorted test3_a1 test3_a2).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((mergeSorted test4_a1 test4_a2).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((mergeSorted test5_a1 test5_a2).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((mergeSorted test6_a1 test6_a2).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((mergeSorted test7_a1 test7_a2).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((mergeSorted test8_a1 test8_a2).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((mergeSorted test9_a1 test9_a2).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((mergeSorted test10_a1 test10_a2).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 189, Column 0
-- Message: unsolved goals
-- case refine_2.refine_2
-- a1 a2 result : Array ℕ
-- ⊢ Decidable (ensures3 a1 a2 result)
-- Line: prove_postcondition_decidable_for mergeSorted
-- [ERROR] Line 191, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
--
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for mergeSorted
-- prove_precondition_decidable_for mergeSorted
-- prove_postcondition_decidable_for mergeSorted
-- derive_tester_for mergeSorted
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Array Nat)
--     let arg_1 ← Plausible.SampleableExt.interpSample (Array Nat)
--     let res := mergeSortedTester arg_0 arg_1
--     pure ((arg_0, arg_1), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break

end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct mergeSorted by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_j_bound : j ≤ a2.size)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_not_i_lt : a1.size ≤ i)
    : j < a2.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_1
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_j_lt_a2 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_in_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_not_i_lt : a1.size ≤ i)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a2[j]!)[i']! = result[i']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_2
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_j_lt_a2 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_in_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_getElem_i' : (result.push a2[j]!)[i']! = result[i']!)
    (h_not_i_lt : a1.size ≤ i)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a2[j]!)[j']! = result[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_3
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_j_lt_a2 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_in_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_getElem_i' : (result.push a2[j]!)[i']! = result[i']!)
    (h_getElem_j' : (result.push a2[j]!)[j']! = result[j']!)
    (h_orig_sorted : result[i']! ≤ result[j']!)
    (h_not_i_lt : a1.size ≤ i)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_4
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_j_lt_a2 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_eq_size : j' = result.size)
    (h_not_i_lt : a1.size ≤ i)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a2[j]!)[j']! = a2[j]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_5
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_j_lt_a2 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_not_i_lt : a1.size ≤ i)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    : result = #[] ∨ 0 < result.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_6
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_j_lt_a2 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_not_i_lt : a1.size ≤ i)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    (h_empty : result = #[])
    : False := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_7
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_not_i_lt : ¬i < a1.size)
    (h_j_lt_a2 : j < a2.size)
    (h_new_size : (result.push a2[j]!).size = result.size + 1)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_lt_new_size : j' < (result.push a2[j]!).size)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_empty : result.size = 0)
    (h_i'_impossible : i' < 0)
    : (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_8
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_j_lt_a2 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_i'_lt_orig : i' < result.size)
    (h_not_i_lt : a1.size ≤ i)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    (h_nonempty : 0 < result.size)
    : (result.push a2[j]!)[i']! = result[i']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_9
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_sorted_inv : isSortedArray result)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_orig : i' < result.size)
    (h_nonempty : 0 < result.size)
    : result[i']! ≤ result[result.size - 1]! := by
    have h_le_pred : i' ≤ result.size - 1 := Nat.le_pred_of_lt h_i'_lt_orig
    cases Nat.lt_or_eq_of_le h_le_pred with
    | inl h_lt =>
      -- i' < result.size - 1, so we can apply sorted invariant
      have h_pred_lt : result.size - 1 < result.size := Nat.sub_one_lt (Nat.ne_of_gt h_nonempty)
      exact invariant_sorted_inv i' (result.size - 1) h_lt h_pred_lt
    | inr h_eq =>
      -- i' = result.size - 1, so result[i']! = result[result.size - 1]!
      rw [h_eq]


theorem goal_0_10
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_j_lt_a2 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_i'_lt_orig : i' < result.size)
    (h_getElem_i' : (result.push a2[j]!)[i']! = result[i']!)
    (h_last_le : result[result.size - 1]! ≤ a2[j]!)
    (h_i'_le_last : result[i']! ≤ result[result.size - 1]!)
    (h_result_elem_le : result[i']! ≤ a2[j]!)
    (h_not_i_lt : a1.size ≤ i)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    (h_nonempty : 0 < result.size)
    : (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_j_bound : j ≤ a2.size)
    (invariant_size_inv : result.size = i + j)
    (invariant_sorted_inv : isSortedArray result)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    : isSortedArray (result.push a2[j]!) := by
    -- From if_pos and if_pos_1, derive that j < a2.size
    have h_not_i_lt : ¬(i < a1.size) := by (try simp at *; expose_names); exact if_pos_1; done
    have h_j_lt_a2 : j < a2.size := by (try simp at *; expose_names); exact (goal_0_0 a1 a2 i j result invariant_j_bound if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_not_i_lt); done
    -- The size of the new array
    have h_new_size : (result.push a2[j]!).size = result.size + 1 := by (try simp at *; expose_names); exact (Array.size_push a2[j]!); done
    -- Unfold the definition of isSortedArray for the pushed array
    unfold isSortedArray
    intro i' j' h_i'_lt_j' h_j'_lt_new_size
    -- Case split: is j' within the original array or is it the new element?
    have h_j'_cases : j' < result.size ∨ j' = result.size := by (try simp at *; expose_names); exact (Nat.lt_succ_iff_lt_or_eq.mp h_j'_lt_new_size); done
    cases h_j'_cases with
    | inl h_j'_in_orig =>
      -- Both i' and j' are in the original result array
      have h_i'_lt_orig : i' < result.size := by (try simp at *; expose_names); exact (Nat.lt_trans h_i'_lt_j' h_j'_in_orig); done
      have h_getElem_i' : (result.push a2[j]!)[i']! = result[i']! := by (try simp at *; expose_names); exact (goal_0_1 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_j_lt_a2 i' j' h_i'_lt_j' h_j'_in_orig h_i'_lt_orig h_not_i_lt h_new_size h_j'_lt_new_size); done
      have h_getElem_j' : (result.push a2[j]!)[j']! = result[j']! := by (try simp at *; expose_names); exact (goal_0_2 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_j_lt_a2 i' j' h_i'_lt_j' h_j'_in_orig h_i'_lt_orig h_getElem_i' h_not_i_lt h_new_size h_j'_lt_new_size); done
      have h_orig_sorted : result[i']! ≤ result[j']! := by (try simp at *; expose_names); exact (invariant_sorted_inv i' j' h_i'_lt_j' h_j'_in_orig); done
      (try simp at *; expose_names); exact (goal_0_3 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_j_lt_a2 i' j' h_i'_lt_j' h_j'_in_orig h_i'_lt_orig h_getElem_i' h_getElem_j' h_orig_sorted h_not_i_lt h_new_size h_j'_lt_new_size); done
    | inr h_j'_eq_size =>
      -- j' is the index of the newly pushed element
      have h_getElem_new : (result.push a2[j]!)[j']! = a2[j]! := by (try simp at *; expose_names); exact (goal_0_4 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_j_lt_a2 i' j' h_i'_lt_j' h_j'_eq_size h_not_i_lt h_new_size h_j'_lt_new_size); done
      -- Case split on whether result is empty
      have h_result_cases : result.size = 0 ∨ result.size > 0 := by (try simp at *; expose_names); exact (goal_0_5 a1 a2 i j result invariant_size_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_j_lt_a2 i' j' h_i'_lt_j' h_j'_eq_size h_getElem_new h_not_i_lt h_new_size h_j'_lt_new_size); done
      cases h_result_cases with
      | inl h_empty =>
        -- Result was empty, so i' < 0 is impossible
        have h_i'_impossible : i' < 0 := by (try simp at *; expose_names); exact (goal_0_6 a1 a2 i j result invariant_size_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_j_lt_a2 i' j' h_i'_lt_j' h_j'_eq_size h_getElem_new h_not_i_lt h_new_size h_j'_lt_new_size h_empty); done
        (try simp at *; expose_names); exact (goal_0_7 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_not_i_lt h_j_lt_a2 h_new_size i' j' h_i'_lt_j' h_j'_lt_new_size h_j'_eq_size h_getElem_new h_empty h_i'_impossible); done
      | inr h_nonempty =>
        -- Result is non-empty
        have h_i'_lt_orig : i' < result.size := by (try simp at *; expose_names); exact (Nat.lt_of_lt_of_eq h_i'_lt_j' h_j'_eq_size); done
        have h_getElem_i' : (result.push a2[j]!)[i']! = result[i']! := by (try simp at *; expose_names); exact (goal_0_8 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_j_lt_a2 i' j' h_i'_lt_j' h_j'_eq_size h_getElem_new h_i'_lt_orig h_not_i_lt h_new_size h_j'_lt_new_size h_nonempty); done
        -- The last element of result is ≤ a2[j]!
        have h_last_le : result[result.size - 1]! ≤ a2[j]! := by (try simp at *; expose_names); exact (invariant_last_le_a2 h_nonempty h_j_lt_a2); done
        -- Since result is sorted, result[i']! ≤ result[result.size - 1]!
        have h_i'_le_last : result[i']! ≤ result[result.size - 1]! := by (try simp at *; expose_names); exact (goal_0_9 a1 a2 i j result invariant_sorted_inv i' j' h_i'_lt_orig h_nonempty); done
        -- By transitivity
        have h_result_elem_le : result[i']! ≤ a2[j]! := by (try simp at *; expose_names); exact (Nat.le_trans h_i'_le_last (invariant_last_le_a2 h_nonempty h_j_lt_a2)); done
        (try simp at *; expose_names); exact (goal_0_10 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_j_lt_a2 i' j' h_i'_lt_j' h_j'_eq_size h_getElem_new h_i'_lt_orig h_getElem_i' h_last_le h_i'_le_last h_result_elem_le h_not_i_lt h_new_size h_j'_lt_new_size h_nonempty); done

theorem goal_1_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (v : ℕ)
    : countInArray (result.push a2[j]!) v = Array.count v result + List.count v [a2[j]!] := by
    unfold countInArray
    simp only [Array.toList_push, List.count_append, Array.count_toList]


theorem goal_1_1
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (v : ℕ)
    (h_countInArray_def : countInArray (result.push a2[j]!) v = Array.count v result + List.count v [a2[j]!])
    : countInArray (result.push a2[j]!) v = countInArray result v + List.count v [a2[j]!] := by
    -- countInArray result v = result.toList.count v by definition
    -- Array.count v result = result.toList.count v by Array.count_toList (reversed)
    -- So countInArray result v = Array.count v result
    unfold countInArray at h_countInArray_def ⊢
    -- Now h_countInArray_def : (result.push a2[j]!).toList.count v = Array.count v result + List.count v [a2[j]!]
    -- Goal: (result.push a2[j]!).toList.count v = result.toList.count v + List.count v [a2[j]!]
    -- We need Array.count v result = result.toList.count v
    have h_eq : Array.count v result = result.toList.count v := by
      rw [← Array.count_toList]
    rw [h_eq] at h_countInArray_def
    exact h_countInArray_def


theorem goal_1_2
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (v : ℕ)
    : List.take (j + 1) a2.toList = List.take j a2.toList ++ a2[j]?.toList := by
  rw [List.take_succ]
  congr 1
  rw [Array.getElem?_toList]


theorem goal_1_3
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_j_lt : j < a2.size)
    (v : ℕ)
    (h_count_push : countInArray (result.push a2[j]!) v = countInArray result v + List.count v [a2[j]!])
    (h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (h_countInArray_def : countInArray (result.push a2[j]!) v = Array.count v result + List.count v [a2[j]!])
    (h_push_toList : True)
    (h_count_append : True)
    (h_take_succ : List.take (j + 1) a2.toList = List.take j a2.toList ++ a2[j]?.toList)
    : a2[j]? = some a2[j]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_1_4
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    (h_j_lt : j < a2.size)
    (v : ℕ)
    (h_count_push : countInArray (result.push a2[j]!) v = countInArray result v + List.count v [a2[j]!])
    (h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (h_countInArray_def : countInArray (result.push a2[j]!) v = Array.count v result + List.count v [a2[j]!])
    (h_push_toList : True)
    (h_count_append : True)
    (h_take_succ : List.take (j + 1) a2.toList = List.take j a2.toList ++ a2[j]?.toList)
    (h_getElem_some : a2[j]? = some a2[j]!)
    (h_option_toList : a2[j]? = some a2[j]!)
    : List.take (j + 1) a2.toList = List.take j a2.toList ++ [a2[j]!] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_1_5
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (v : ℕ)
    (h_take_succ_eq : List.take (j + 1) a2.toList = List.take j a2.toList ++ [a2[j]!])
    : countInArray { toList := List.take (j + 1) a2.toList } v = countInArray { toList := List.take j a2.toList } v + List.count v [a2[j]!] := by
    unfold countInArray
    simp only []
    rw [h_take_succ_eq]
    rw [List.count_append]

theorem goal_1
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_j_bound : j ≤ a2.size)
    (invariant_count_inv : ∀ (v : ℕ), countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_pos_1 : a1.size ≤ i)
    : ∀ (v : ℕ), countInArray (result.push a2[j]!) v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take (j + 1) a2.toList } v := by
    -- Since i ≥ a1.size and (i < a1.size ∨ j < a2.size), we must have j < a2.size
    have h_j_lt : j < a2.size := by (try simp at *; expose_names); exact (goal_0_0 a1 a2 i j result invariant_j_bound if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 if_pos_1); done
    -- Introduce the universally quantified variable
    intro v
    -- Unfold the definition of countInArray
    have h_countInArray_def : countInArray (result.push a2[j]!) v = (result.push a2[j]!).toList.count v := by (try simp at *; expose_names); exact (goal_1_0 a1 a2 i j result v); done
    -- The pushed array's toList is the original toList with the element appended
    have h_push_toList : (result.push a2[j]!).toList = result.toList ++ [a2[j]!] := by (try simp at *; expose_names); exact (Array.toList_push); done
    -- Count over append equals sum of counts
    have h_count_append : (result.toList ++ [a2[j]!]).count v = result.toList.count v + [a2[j]!].count v := by (try simp at *; expose_names); exact (List.count_append); done
    -- So count in pushed array equals count in result plus count in singleton
    have h_count_push : countInArray (result.push a2[j]!) v = countInArray result v + [a2[j]!].count v := by (try simp at *; expose_names); exact (goal_1_1 a1 a2 i j result v h_countInArray_def); done
    -- Apply the invariant for the original result
    have h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v := by (try simp at *; expose_names); exact (invariant_count_inv v); done
    -- List.take (j+1) equals List.take j ++ [a2[j]] when j < a2.size
    have h_take_succ : List.take (j + 1) a2.toList = List.take j a2.toList ++ (a2.toList[j]?).toList := by (try simp at *; expose_names); exact (goal_1_2 a1 a2 i j result v); done
    -- Connect a2[j]! with a2.toList[j]
    have h_getElem_some : a2.toList[j]? = some a2[j]! := by (try simp at *; expose_names); exact (goal_1_3 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_j_lt v h_count_push h_inv_applied h_countInArray_def h_push_toList h_count_append h_take_succ); done
    -- So the toList of Option is [a2[j]!]
    have h_option_toList : (a2.toList[j]?).toList = [a2[j]!] := by (try simp at *; expose_names); exact (h_getElem_some); done
    -- Therefore take (j+1) = take j ++ [a2[j]!]
    have h_take_succ_eq : List.take (j + 1) a2.toList = List.take j a2.toList ++ [a2[j]!] := by (try simp at *; expose_names); exact (goal_1_4 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1 h_j_lt v h_count_push h_inv_applied h_countInArray_def h_push_toList h_count_append h_take_succ h_getElem_some h_option_toList); done
    -- Count in take (j+1) equals count in take j plus count in singleton
    have h_count_take_succ : countInArray { toList := List.take (j + 1) a2.toList } v = countInArray { toList := List.take j a2.toList } v + [a2[j]!].count v := by (try simp at *; expose_names); exact (goal_1_5 a1 a2 i j result v h_take_succ_eq); done
    -- Combine everything to get the final equality
    calc countInArray (result.push a2[j]!) v
        = countInArray result v + [a2[j]!].count v := h_count_push
      _ = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v + [a2[j]!].count v := by (try simp at *; expose_names); exact (invariant_count_inv v); done
      _ = countInArray { toList := List.take i a1.toList } v + (countInArray { toList := List.take j a2.toList } v + [a2[j]!].count v) := by (try simp at *; expose_names); exact (Nat.add_assoc (countInArray { toList := List.take i a1.toList } v) (countInArray { toList := List.take j a2.toList } v) (List.count v [a2[j]!])); done
      _ = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take (j + 1) a2.toList } v := by (try simp at *; expose_names); exact (id (Eq.symm h_count_take_succ)); done

theorem goal_2
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (require_1 : precondition a1 a2)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    : j + 1 < a2.size → a2[j]! ≤ a2[j + 1]! := by
    intro h_j_succ_lt
    -- Extract that a2 is sorted from the precondition
    have h_sorted_a2 : isSortedArray a2 := require_1.2
    -- isSortedArray means: ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!
    unfold isSortedArray at h_sorted_a2
    -- Apply with indices j and j+1
    have h_j_lt_j_succ : j < j + 1 := Nat.lt_succ_self j
    exact h_sorted_a2 j (j + 1) h_j_lt_j_succ h_j_succ_lt

theorem goal_3_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_pos_1 : a2.size ≤ j)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_le_result_size : j' ≤ result.size)
    (h_j'_lt_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a1[i]!)[i']! = result[i']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_3_1
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_pos_1 : a2.size ≤ j)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_le_result_size : j' ≤ result.size)
    (h_j'_lt_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_getElem_i' : (result.push a1[i]!)[i']! = result[i']!)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a1[i]!)[j']! = result[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_3_2
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_pos_1 : a2.size ≤ j)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_le_result_size : j' ≤ result.size)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a1[i]!)[j']! = a1[i]!)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    : result = #[] ∨ 0 < result.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_3_3
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_pos_1 : a2.size ≤ j)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_le_result_size : j' ≤ result.size)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a1[i]!)[j']! = a1[i]!)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    (h_empty : result = #[])
    : j' = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_3_4
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_pos_1 : a2.size ≤ j)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_le_result_size : j' ≤ result.size)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a1[i]!)[j']! = a1[i]!)
    (h_j'_eq_zero : j' = 0)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    (h_empty : result = #[])
    : False := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_3_5
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_pos_1 : a2.size ≤ j)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_le_result_size : j' ≤ result.size)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a1[i]!)[j']! = a1[i]!)
    (h_nonempty : 0 < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_new_size : True)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a1[i]!)[i']! = result[i']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_3
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (invariant_sorted_inv : isSortedArray result)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_pos_1 : a2.size ≤ j)
    : isSortedArray (result.push a1[i]!) := by
    -- First establish the new size after push
    have h_new_size : (result.push a1[i]!).size = result.size + 1 := by (try simp at *; expose_names); exact (Array.size_push a1[i]!); done
    -- Unfold the definition of isSortedArray and introduce indices
    unfold isSortedArray
    intro i' j' h_i'_lt_j' h_j'_lt_new_size
    -- Convert the bound on j' using the new size
    have h_j'_le_result_size : j' ≤ result.size := by (try simp at *; expose_names); exact (Nat.le_of_lt_succ h_j'_lt_new_size); done
    -- Case split: either j' < result.size (both indices in original) or j' = result.size (new element)
    have h_cases : j' < result.size ∨ j' = result.size := by (try simp at *; expose_names); exact (Nat.lt_succ_iff_lt_or_eq.mp h_j'_lt_new_size); done
    cases h_cases with
    | inl h_j'_lt_orig =>
      -- Both i' and j' are in the original result
      have h_i'_lt_orig : i' < result.size := by (try simp at *; expose_names); exact (Nat.lt_of_lt_of_le h_i'_lt_j' h_j'_le_result_size); done
      -- Elements at positions less than original size are unchanged after push
      have h_getElem_i' : (result.push a1[i]!)[i']! = result[i']! := by (try simp at *; expose_names); exact (goal_3_0 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_pos_1 i' j' h_i'_lt_j' h_j'_le_result_size h_j'_lt_orig h_i'_lt_orig h_new_size h_j'_lt_new_size); done
      have h_getElem_j' : (result.push a1[i]!)[j']! = result[j']! := by (try simp at *; expose_names); exact (goal_3_1 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_pos_1 i' j' h_i'_lt_j' h_j'_le_result_size h_j'_lt_orig h_i'_lt_orig h_getElem_i' h_new_size h_j'_lt_new_size); done
      -- By invariant_sorted_inv, result is sorted
      have h_orig_sorted : result[i']! ≤ result[j']! := by (try simp at *; expose_names); exact (invariant_sorted_inv i' j' h_i'_lt_j' h_j'_lt_orig); done
      -- Combine to get the result
      have h_final : (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']! := by (try simp at *; expose_names); exact (goal_0_3 a2 a1 j i result (id (Or.symm if_pos)) invariant_last_le_a2 invariant_last_le_a1 if_pos_1 if_neg i' j' h_i'_lt_j' h_j'_lt_orig h_i'_lt_orig h_getElem_i' h_getElem_j' (invariant_sorted_inv i' j' h_i'_lt_j' h_j'_lt_orig) if_pos_1 h_new_size h_j'_lt_new_size); done
      exact h_final
    | inr h_j'_eq_size =>
      -- j' is the new element position
      have h_getElem_new : (result.push a1[i]!)[j']! = a1[i]! := by (try simp at *; expose_names); exact (goal_0_4 a2 a1 j i result (id (Or.symm if_pos)) invariant_last_le_a2 invariant_last_le_a1 if_pos_1 if_neg i' j' h_i'_lt_j' h_j'_eq_size if_pos_1 h_new_size h_j'_lt_new_size); done
      -- Check if result is empty or not
      have h_empty_or_nonempty : result.size = 0 ∨ 0 < result.size := by (try simp at *; expose_names); exact (goal_3_2 a1 a2 i j result invariant_size_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_pos_1 i' j' h_i'_lt_j' h_j'_le_result_size h_j'_eq_size h_getElem_new h_new_size h_j'_lt_new_size); done
      cases h_empty_or_nonempty with
      | inl h_empty =>
        -- If result is empty, i' < j' = 0 is impossible
        have h_j'_eq_zero : j' = 0 := by (try simp at *; expose_names); exact (goal_3_3 a1 a2 i j result invariant_size_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_pos_1 i' j' h_i'_lt_j' h_j'_le_result_size h_j'_eq_size h_getElem_new h_new_size h_j'_lt_new_size h_empty); done
        have h_i'_lt_zero : i' < 0 := by (try simp at *; expose_names); exact (goal_3_4 a1 a2 i j result invariant_size_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_pos_1 i' j' h_i'_lt_j' h_j'_le_result_size h_j'_eq_size h_getElem_new h_j'_eq_zero h_new_size h_j'_lt_new_size h_empty); done
        exact absurd h_i'_lt_zero (Nat.not_lt_zero i')
      | inr h_nonempty =>
        -- result is non-empty
        have h_i'_lt_orig : i' < result.size := by (try simp at *; expose_names); exact (Nat.lt_of_lt_of_le h_i'_lt_j' h_j'_le_result_size); done
        -- Element at i' is unchanged after push
        have h_getElem_i' : (result.push a1[i]!)[i']! = result[i']! := by (try simp at *; expose_names); exact (goal_3_5 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_pos_1 i' j' h_i'_lt_j' h_j'_le_result_size h_j'_eq_size h_getElem_new h_nonempty h_i'_lt_orig h_new_size h_j'_lt_new_size); done
        -- By invariant_last_le_a1, last element of result ≤ a1[i]!
        have h_last_le_a1i : result[result.size - 1]! ≤ a1[i]! := by (try simp at *; expose_names); exact (invariant_last_le_a1 h_nonempty if_neg); done
        -- By sortedness, result[i']! ≤ result[result.size - 1]!
        have h_i'_le_last : result[i']! ≤ result[result.size - 1]! := by (try simp at *; expose_names); exact (goal_0_9 a1 a1 i i result invariant_sorted_inv i' i h_i'_lt_orig h_nonempty); done
        -- By transitivity
        have h_i'_le_a1i : result[i']! ≤ a1[i]! := by (try simp at *; expose_names); exact (Nat.le_trans h_i'_le_last (invariant_last_le_a1 h_nonempty if_neg)); done
        -- Combine
        have h_final : (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']! := by (try simp at *; expose_names); exact (goal_0_10 a2 a1 j i result (id (Or.symm if_pos)) invariant_last_le_a2 invariant_last_le_a1 if_pos_1 if_neg i' j' h_i'_lt_j' h_j'_eq_size h_getElem_new h_i'_lt_orig h_getElem_i' (invariant_last_le_a1 h_nonempty if_neg) h_i'_le_last h_i'_le_a1i if_pos_1 h_new_size h_j'_lt_new_size h_nonempty); done
        exact h_final

theorem goal_4_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (v : ℕ)
    : countInArray (result.push a1[i]!) v = countInArray result v + List.count v [a1[i]!] := by
    unfold countInArray
    simp only [Array.toList_push, List.count_append]


theorem goal_4_1
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_pos_1 : a2.size ≤ j)
    (v : ℕ)
    (h_count_push : countInArray (result.push a1[i]!) v = countInArray result v + List.count v [a1[i]!])
    (h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (h_push_toList : True)
    : a1[i]? = some a1[i]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_4_2
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (v : ℕ)
    (h_getElem_some : a1[i]? = some a1[i]!)
    : List.take (i + 1) a1.toList = List.take i a1.toList ++ [a1[i]!] := by
    rw [List.take_succ]
    congr 1
    rw [Array.getElem?_toList]
    rw [h_getElem_some]
    rfl


theorem goal_4_3
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_pos_1 : a2.size ≤ j)
    (v : ℕ)
    (h_count_push : countInArray (result.push a1[i]!) v = countInArray result v + List.count v [a1[i]!])
    (h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (h_take_succ : List.take (i + 1) a1.toList = List.take i a1.toList ++ [a1[i]!])
    (h_count_take_succ : countInArray { toList := List.take (i + 1) a1.toList } v = countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!])
    (h_rearrange : countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!] + countInArray { toList := List.take j a2.toList } v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v + List.count v [a1[i]!])
    (h_push_toList : True)
    (h_getElem_some : a1[i]? = some a1[i]!)
    (h_rhs_rewrite : countInArray { toList := List.take (i + 1) a1.toList } v = countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!])
    : countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v + List.count v [a1[i]!] = countInArray { toList := List.take (i + 1) a1.toList } v + countInArray { toList := List.take j a2.toList } v := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_4
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_count_inv : ∀ (v : ℕ), countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_pos_1 : a2.size ≤ j)
    : ∀ (v : ℕ), countInArray (result.push a1[i]!) v = countInArray { toList := List.take (i + 1) a1.toList } v + countInArray { toList := List.take j a2.toList } v := by
    intro v
    -- Step 1: Express count after push in terms of count before push
    have h_push_toList : (result.push a1[i]!).toList = result.toList ++ [a1[i]!] := by (try simp at *; expose_names); exact (Array.toList_push); done
    -- Step 2: Count in pushed array equals count in result plus count in singleton
    have h_count_push : countInArray (result.push a1[i]!) v = countInArray result v + List.count v [a1[i]!] := by (try simp at *; expose_names); exact (goal_4_0 a1 a2 i j result v); done
    -- Step 3: Apply the invariant to express countInArray result v
    have h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v := by (try simp at *; expose_names); exact (invariant_count_inv v); done
    -- Step 4: Show that a1[i]? = some a1[i]! since i < a1.size
    have h_getElem_some : a1.toList[i]? = some a1[i]! := by (try simp at *; expose_names); exact (goal_4_1 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_pos_1 v h_count_push h_inv_applied h_push_toList); done
    -- Step 5: Show List.take (i + 1) a1.toList = List.take i a1.toList ++ [a1[i]!]
    have h_take_succ : List.take (i + 1) a1.toList = List.take i a1.toList ++ [a1[i]!] := by (try simp at *; expose_names); exact (goal_4_2 a1 a2 i j result v h_getElem_some); done
    -- Step 6: Count in take (i+1) equals count in take i plus count in singleton
    have h_count_take_succ : countInArray { toList := List.take (i + 1) a1.toList } v = countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!] := by (try simp at *; expose_names); exact (goal_1_5 a1 a1 i i a1 v h_take_succ); done
    -- Step 7: Combine all the equalities
    have h_rhs_rewrite : countInArray { toList := List.take (i + 1) a1.toList } v + countInArray { toList := List.take j a2.toList } v = countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!] + countInArray { toList := List.take j a2.toList } v := by (try simp at *; expose_names); exact (h_count_take_succ); done
    -- Step 8: Use commutativity and associativity to rearrange
    have h_rearrange : countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!] + countInArray { toList := List.take j a2.toList } v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v + List.count v [a1[i]!] := by (try simp at *; expose_names); exact (Nat.add_right_comm (countInArray { toList := List.take i a1.toList } v) (List.count v [a1[i]!]) (countInArray { toList := List.take j a2.toList } v)); done
    -- Final: Combine everything
    calc countInArray (result.push a1[i]!) v
        = countInArray result v + List.count v [a1[i]!] := h_count_push
      _ = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v + List.count v [a1[i]!] := by (try simp at *; expose_names); exact (invariant_count_inv v); done
      _ = countInArray { toList := List.take (i + 1) a1.toList } v + countInArray { toList := List.take j a2.toList } v := by (try simp at *; expose_names); exact (goal_4_3 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_pos_1 v h_count_push h_inv_applied h_take_succ h_count_take_succ h_rearrange h_push_toList h_getElem_some h_rhs_rewrite); done

theorem goal_5
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (require_1 : precondition a1 a2)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    : i + 1 < a1.size → a1[i]! ≤ a1[i + 1]! := by
    intro h_i_succ_lt
    -- Extract that a1 is sorted from the precondition
    have h_a1_sorted : isSortedArray a1 := require_1.1
    -- Unfold the definition of isSortedArray
    unfold isSortedArray at h_a1_sorted
    -- Apply the sorted property with i and i+1
    have h_i_lt_succ : i < i + 1 := Nat.lt_succ_self i
    exact h_a1_sorted i (i + 1) h_i_lt_succ h_i_succ_lt

theorem goal_6_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']! := by
    unfold isSortedArray
    simp only [Array.size_push]


theorem goal_6_1
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_lt_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_new_size : True)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a1[i]!)[i']! = result[i']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_6_2
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_lt_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_getElem_i' : (result.push a1[i]!)[i']! = result[i']!)
    (h_new_size : True)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a1[i]!)[j']! = result[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_6_3
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_lt_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_getElem_i' : (result.push a1[i]!)[i']! = result[i']!)
    (h_getElem_j' : (result.push a1[i]!)[j']! = result[j']!)
    (h_orig_sorted : result[i']! ≤ result[j']!)
    (h_new_size : True)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_6_4
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_new_size : True)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a1[i]!)[j']! = a1[i]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_6_5
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a1[i]!)[j']! = a1[i]!)
    (h_new_size : True)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (h_j'_lt_new_size : j' < result.size + 1)
    : result = #[] ∨ 0 < result.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_6_6
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a1[i]!)[j']! = a1[i]!)
    (h_new_size : True)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (h_j'_lt_new_size : j' < result.size + 1)
    (h_empty : result = #[])
    : j' = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_6_7
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a1[i]!)[j']! = a1[i]!)
    (h_j'_eq_zero : j' = 0)
    (h_new_size : True)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (h_j'_lt_new_size : j' < result.size + 1)
    (h_empty : result = #[])
    : False := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_6_8
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (h_new_size : (result.push a1[i]!).size = result.size + 1)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < (result.push a1[i]!).size → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_lt_new_size : j' < (result.push a1[i]!).size)
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a1[i]!)[j']! = a1[i]!)
    (h_empty : result.size = 0)
    (h_j'_eq_zero : j' = 0)
    (h_i'_impossible : i' < 0)
    : (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_6_9
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a1[i]!)[j']! = a1[i]!)
    (h_nonempty : 0 < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_new_size : True)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a1[i]!)[i']! = result[i']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_6_10
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a1[i]!)[j']! = a1[i]!)
    (h_nonempty : 0 < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_getElem_i' : (result.push a1[i]!)[i']! = result[i']!)
    (h_i'_le_last : result[i']! ≤ result[result.size - 1]!)
    (h_last_le_a1i : result[result.size - 1]! ≤ a1[i]!)
    (h_trans : result[i']! ≤ a1[i]!)
    (h_new_size : True)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (h_j'_lt_new_size : j' < result.size + 1)
    : (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_6_11
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (h_new_size : True)
    (h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    (h_prove_sorted : ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']!)
    : isSortedArray (result.push a1[i]!) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_6
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (invariant_sorted_inv : isSortedArray result)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    : isSortedArray (result.push a1[i]!) := by
    have h_new_size : (result.push a1[i]!).size = result.size + 1 := by (try simp at *; expose_names); exact (Array.size_push a1[i]!); done
    have h_unfold_sorted : isSortedArray (result.push a1[i]!) ↔
      ∀ i' j' : ℕ, i' < j' → j' < (result.push a1[i]!).size → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']! := by (try simp at *; expose_names); exact (goal_6_0 a1 a2 i j result); done
    have h_prove_sorted : ∀ i' j' : ℕ, i' < j' → j' < (result.push a1[i]!).size → (result.push a1[i]!)[i']! ≤ (result.push a1[i]!)[j']! := by
      intro i' j' h_i'_lt_j' h_j'_lt_new_size
      have h_j'_bound : j' < result.size + 1 := by (try simp at *; expose_names); exact (h_j'_lt_new_size); done
      have h_j'_cases : j' < result.size ∨ j' = result.size := by (try simp at *; expose_names); exact (Nat.lt_succ_iff_lt_or_eq.mp h_j'_bound); done
      cases h_j'_cases with
      | inl h_j'_lt_orig =>
        have h_i'_lt_orig : i' < result.size := by (try simp at *; expose_names); exact (Nat.lt_trans h_i'_lt_j' h_j'_lt_orig); done
        have h_getElem_i' : (result.push a1[i]!)[i']! = result[i']! := by (try simp at *; expose_names); exact (goal_6_1 a1 a2 i j result if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 i' j' h_i'_lt_j' h_j'_bound h_j'_lt_orig h_i'_lt_orig h_new_size h_unfold_sorted h_j'_lt_new_size); done
        have h_getElem_j' : (result.push a1[i]!)[j']! = result[j']! := by (try simp at *; expose_names); exact (goal_6_2 a1 a2 i j result if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 i' j' h_i'_lt_j' h_j'_bound h_j'_lt_orig h_i'_lt_orig h_getElem_i' h_new_size h_unfold_sorted h_j'_lt_new_size); done
        have h_orig_sorted : result[i']! ≤ result[j']! := by (try simp at *; expose_names); exact (invariant_sorted_inv i' j' h_i'_lt_j' h_j'_lt_orig); done
        (try simp at *; expose_names); exact (goal_6_3 a1 a2 i j result if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 i' j' h_i'_lt_j' h_j'_bound h_j'_lt_orig h_i'_lt_orig h_getElem_i' h_getElem_j' h_orig_sorted h_new_size h_unfold_sorted h_j'_lt_new_size); done
      | inr h_j'_eq_size =>
        have h_getElem_new : (result.push a1[i]!)[j']! = a1[i]! := by (try simp at *; expose_names); exact (goal_6_4 a1 a2 i j result if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_new_size h_unfold_sorted h_j'_lt_new_size); done
        have h_empty_or_nonempty : result.size = 0 ∨ 0 < result.size := by (try simp at *; expose_names); exact (goal_6_5 a1 a2 i j result invariant_size_inv if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_new_size h_unfold_sorted h_j'_lt_new_size); done
        cases h_empty_or_nonempty with
        | inl h_empty =>
          have h_j'_eq_zero : j' = 0 := by (try simp at *; expose_names); exact (goal_6_6 a1 a2 i j result invariant_size_inv if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_new_size h_unfold_sorted h_j'_lt_new_size h_empty); done
          have h_i'_impossible : i' < 0 := by (try simp at *; expose_names); exact (goal_6_7 a1 a2 i j result invariant_size_inv if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_j'_eq_zero h_new_size h_unfold_sorted h_j'_lt_new_size h_empty); done
          (try simp at *; expose_names); exact (goal_6_8 a1 a2 i j result if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 h_new_size h_unfold_sorted i' j' h_i'_lt_j' h_j'_lt_new_size h_j'_bound h_j'_eq_size h_getElem_new h_empty h_j'_eq_zero h_i'_impossible); done
        | inr h_nonempty =>
          have h_i'_lt_orig : i' < result.size := by (try simp at *; expose_names); exact (Nat.lt_of_lt_of_eq h_i'_lt_j' h_j'_eq_size); done
          have h_getElem_i' : (result.push a1[i]!)[i']! = result[i']! := by (try simp at *; expose_names); exact (goal_6_9 a1 a2 i j result if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_nonempty h_i'_lt_orig h_new_size h_unfold_sorted h_j'_lt_new_size); done
          have h_i'_le_last : result[i']! ≤ result[result.size - 1]! := by (try simp at *; expose_names); exact (goal_0_9 a1 a1 i i result invariant_sorted_inv i' i h_i'_lt_orig h_nonempty); done
          have h_last_le_a1i : result[result.size - 1]! ≤ a1[i]! := by (try simp at *; expose_names); exact (invariant_last_le_a1 h_nonempty if_neg); done
          have h_trans : result[i']! ≤ a1[i]! := by (try simp at *; expose_names); exact (Nat.le_trans h_i'_le_last (invariant_last_le_a1 h_nonempty if_neg)); done
          (try simp at *; expose_names); exact (goal_6_10 a1 a2 i j result if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_nonempty h_i'_lt_orig h_getElem_i' h_i'_le_last h_last_le_a1i h_trans h_new_size h_unfold_sorted h_j'_lt_new_size); done
    (try simp at *; expose_names); exact (goal_6_11 a1 a2 i j result if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 h_new_size h_unfold_sorted h_prove_sorted); done

theorem goal_7_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (v : ℕ)
    (h_count_push : countInArray (result.push a1[i]!) v = countInArray result v + List.count v [a1[i]!])
    (h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    : a1[i]? = some a1[i]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_7_1
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (v : ℕ)
    (h_count_push : countInArray (result.push a1[i]!) v = countInArray result v + List.count v [a1[i]!])
    (h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (h_getElem_some : a1[i]? = some a1[i]!)
    (h_take_succ : List.take (i + 1) a1.toList = List.take i a1.toList ++ [a1[i]!])
    (h_count_take_succ : countInArray { toList := List.take (i + 1) a1.toList } v = countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!])
    : countInArray (result.push a1[i]!) v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v + List.count v [a1[i]!] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_7
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_count_inv : ∀ (v : ℕ), countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (if_pos : i < a1.size ∨ j < a2.size)
    (if_pos_1 : a1[i]! ≤ a2[j]!)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    : ∀ (v : ℕ), countInArray (result.push a1[i]!) v = countInArray { toList := List.take (i + 1) a1.toList } v + countInArray { toList := List.take j a2.toList } v := by
    intro v
    -- Step 1: Express count after push as count before plus count of singleton
    have h_count_push : countInArray (result.push a1[i]!) v = countInArray result v + List.count v [a1[i]!] := by (try simp at *; expose_names); exact (goal_4_0 a1 a1 i i result v); done
    -- Step 2: Apply the invariant to express countInArray result v
    have h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v := by (try simp at *; expose_names); exact (invariant_count_inv v); done
    -- Step 3: Show that a1[i]? = some a1[i]! since i < a1.size
    have h_getElem_some : a1[i]? = some a1[i]! := by (try simp at *; expose_names); exact (goal_7_0 a1 a2 i j result if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 v h_count_push h_inv_applied); done
    -- Step 4: Show List.take (i + 1) a1.toList = List.take i a1.toList ++ [a1[i]!]
    have h_take_succ : List.take (i + 1) a1.toList = List.take i a1.toList ++ [a1[i]!] := by (try simp at *; expose_names); exact (goal_4_2 a1 a1 i i a1 i h_getElem_some); done
    -- Step 5: Count in take (i+1) equals count in take i plus count in singleton
    have h_count_take_succ : countInArray { toList := List.take (i + 1) a1.toList } v = countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!] := by (try simp at *; expose_names); exact (goal_1_5 a1 a1 i i a1 v h_take_succ); done
    -- Step 6: Combine the equations using substitution
    have h_lhs_expand : countInArray (result.push a1[i]!) v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v + List.count v [a1[i]!] := by (try simp at *; expose_names); exact (goal_7_1 a1 a2 i j result if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 v h_count_push h_inv_applied h_getElem_some h_take_succ h_count_take_succ); done
    -- Step 7: Rearrange using commutativity of addition
    have h_add_rearrange : countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v + List.count v [a1[i]!] = countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!] + countInArray { toList := List.take j a2.toList } v := by (try simp at *; expose_names); exact (Nat.add_right_comm (countInArray { toList := List.take i a1.toList } v) (countInArray { toList := List.take j a2.toList } v) (List.count v [a1[i]!])); done
    -- Step 8: Substitute the count_take_succ result
    have h_rhs_form : countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!] + countInArray { toList := List.take j a2.toList } v = countInArray { toList := List.take (i + 1) a1.toList } v + countInArray { toList := List.take j a2.toList } v := by (try simp at *; expose_names); exact (id (Eq.symm h_count_take_succ)); done
    -- Final: Chain the equalities
    calc countInArray (result.push a1[i]!) v
        = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v + List.count v [a1[i]!] := h_lhs_expand
      _ = countInArray { toList := List.take i a1.toList } v + List.count v [a1[i]!] + countInArray { toList := List.take j a2.toList } v := h_add_rearrange
      _ = countInArray { toList := List.take (i + 1) a1.toList } v + countInArray { toList := List.take j a2.toList } v := h_rhs_form

theorem goal_8
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (require_1 : precondition a1 a2)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    : i + 1 < a1.size → a1[i]! ≤ a1[i + 1]! := by
    intros; expose_names; exact (goal_5 a1 a2 require_1 i i a1 h); done

theorem goal_9_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_lt_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_new_size : True)
    : (result.push a2[j]!)[i']! = result[i']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_9_1
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_lt_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_getElem_i' : (result.push a2[j]!)[i']! = result[i']!)
    (h_new_size : True)
    : (result.push a2[j]!)[j']! = result[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_9_2
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_lt_orig : j' < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_getElem_i' : (result.push a2[j]!)[i']! = result[i']!)
    (h_getElem_j' : (result.push a2[j]!)[j']! = result[j']!)
    (h_orig_sorted : result[i']! ≤ result[j']!)
    (h_new_size : True)
    : (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_9_3
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_new_size : True)
    : (result.push a2[j]!)[j']! = a2[j]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_9_4
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_new_size : True)
    : result = #[] ∨ 0 < result.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_9_5
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_new_size : True)
    (h_empty : result = #[])
    : j' = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_9_6
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_j'_zero : j' = 0)
    (h_new_size : True)
    (h_empty : result = #[])
    : False := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_9_7
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (h_new_size : (result.push a2[j]!).size = result.size + 1)
    (h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_empty : result.size = 0)
    (h_j'_zero : j' = 0)
    (h_i'_impossible : i' < 0)
    : (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_9_8
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_nonempty : 0 < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_new_size : True)
    : (result.push a2[j]!)[i']! = result[i']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_9_9
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']!)
    (i' : ℕ)
    (j' : ℕ)
    (h_i'_lt_j' : i' < j')
    (h_j'_bound : j' < result.size + 1)
    (h_j'_eq_size : j' = result.size)
    (h_getElem_new : (result.push a2[j]!)[j']! = a2[j]!)
    (h_nonempty : 0 < result.size)
    (h_i'_lt_orig : i' < result.size)
    (h_getElem_i' : (result.push a2[j]!)[i']! = result[i']!)
    (h_last_le : result[result.size - 1]! ≤ a2[j]!)
    (h_i'_le_last : result[i']! ≤ result[result.size - 1]!)
    (h_trans : result[i']! ≤ a2[j]!)
    (h_new_size : True)
    : (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_9
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_size_inv : result.size = i + j)
    (invariant_sorted_inv : isSortedArray result)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    : isSortedArray (result.push a2[j]!) := by
    -- The new array has size result.size + 1
    have h_new_size : (result.push a2[j]!).size = result.size + 1 := by (try simp at *; expose_names); exact (Array.size_push a2[j]!); done
    -- Unfold the definition of isSortedArray for the pushed array
    have h_unfold_sorted : isSortedArray (result.push a2[j]!) ↔ ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']! := by (try simp at *; expose_names); exact (goal_6_0 a2 a1 j i result); done
    -- Prove the sorted property for all valid index pairs
    have h_prove_sorted : ∀ (i' j' : ℕ), i' < j' → j' < result.size + 1 → (result.push a2[j]!)[i']! ≤ (result.push a2[j]!)[j']! := by
      intro i' j' h_i'_lt_j' h_j'_bound
      -- Case split: j' < result.size (both in original) vs j' = result.size (j' is new element)
      have h_j'_cases : j' < result.size ∨ j' = result.size := by (try simp at *; expose_names); exact (Nat.lt_succ_iff_lt_or_eq.mp h_j'_bound); done
      cases h_j'_cases with
      | inl h_j'_lt_orig =>
        -- Both i' and j' are in original array
        have h_i'_lt_orig : i' < result.size := by (try simp at *; expose_names); exact (Nat.lt_trans h_i'_lt_j' h_j'_lt_orig); done
        have h_getElem_i' : (result.push a2[j]!)[i']! = result[i']! := by (try simp at *; expose_names); exact (goal_9_0 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 h_unfold_sorted i' j' h_i'_lt_j' h_j'_bound h_j'_lt_orig h_i'_lt_orig h_new_size); done
        have h_getElem_j' : (result.push a2[j]!)[j']! = result[j']! := by (try simp at *; expose_names); exact (goal_9_1 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 h_unfold_sorted i' j' h_i'_lt_j' h_j'_bound h_j'_lt_orig h_i'_lt_orig h_getElem_i' h_new_size); done
        have h_orig_sorted : result[i']! ≤ result[j']! := by (try simp at *; expose_names); exact (invariant_sorted_inv i' j' h_i'_lt_j' h_j'_lt_orig); done
        (try simp at *; expose_names); exact (goal_9_2 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 h_unfold_sorted i' j' h_i'_lt_j' h_j'_bound h_j'_lt_orig h_i'_lt_orig h_getElem_i' h_getElem_j' h_orig_sorted h_new_size); done
      | inr h_j'_eq_size =>
        -- j' is the new element position
        have h_getElem_new : (result.push a2[j]!)[j']! = a2[j]! := by (try simp at *; expose_names); exact (goal_9_3 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 h_unfold_sorted i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_new_size); done
        -- Case split on whether result is empty
        have h_empty_or_not : result.size = 0 ∨ 0 < result.size := by (try simp at *; expose_names); exact (goal_9_4 a1 a2 i j result invariant_size_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 h_unfold_sorted i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_new_size); done
        cases h_empty_or_not with
        | inl h_empty =>
          -- result is empty, so j' = 0 and i' < 0 is impossible
          have h_j'_zero : j' = 0 := by (try simp at *; expose_names); exact (goal_9_5 a1 a2 i j result invariant_size_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 h_unfold_sorted i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_new_size h_empty); done
          have h_i'_impossible : i' < 0 := by (try simp at *; expose_names); exact (goal_9_6 a1 a2 i j result invariant_size_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 h_unfold_sorted i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_j'_zero h_new_size h_empty); done
          (try simp at *; expose_names); exact (goal_9_7 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 h_new_size h_unfold_sorted i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_empty h_j'_zero h_i'_impossible); done
        | inr h_nonempty =>
          -- result is non-empty
          have h_i'_lt_orig : i' < result.size := by (try simp at *; expose_names); exact (Nat.lt_of_lt_of_eq h_i'_lt_j' h_j'_eq_size); done
          have h_getElem_i' : (result.push a2[j]!)[i']! = result[i']! := by (try simp at *; expose_names); exact (goal_9_8 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 h_unfold_sorted i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_nonempty h_i'_lt_orig h_new_size); done
          -- Use invariant_last_le_a2 to get result[result.size - 1]! ≤ a2[j]!
          have h_last_le : result[result.size - 1]! ≤ a2[j]! := by (try simp at *; expose_names); exact (invariant_last_le_a2 h_nonempty if_neg_1); done
          -- Use sortedness to get result[i']! ≤ result[result.size - 1]!
          have h_i'_le_last : result[i']! ≤ result[result.size - 1]! := by (try simp at *; expose_names); exact (goal_0_9 a1 a1 i i result invariant_sorted_inv i' i h_i'_lt_orig h_nonempty); done
          -- By transitivity
          have h_trans : result[i']! ≤ a2[j]! := by (try simp at *; expose_names); exact (Nat.le_trans h_i'_le_last (invariant_last_le_a2 h_nonempty if_neg_1)); done
          (try simp at *; expose_names); exact (goal_9_9 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 h_unfold_sorted i' j' h_i'_lt_j' h_j'_bound h_j'_eq_size h_getElem_new h_nonempty h_i'_lt_orig h_getElem_i' h_last_le h_i'_le_last h_trans h_new_size); done
    -- Apply the equivalence to conclude
    (try simp at *; expose_names); exact (goal_6_0 a2 a1 j i result).mpr h_prove_sorted; done

theorem goal_10_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (v : ℕ)
    (h_count_push : countInArray (result.push a2[j]!) v = countInArray result v + List.count v [a2[j]!])
    (h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (h_j_lt_size : j < a2.size)
    (h_push_toList : True)
    : a2[j]? = some a2[j]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_10_1
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    (v : ℕ)
    (h_count_push : countInArray (result.push a2[j]!) v = countInArray result v + List.count v [a2[j]!])
    (h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (h_j_lt_size : j < a2.size)
    (h_getElem_some : a2[j]? = some a2[j]!)
    (h_take_succ : List.take (j + 1) a2.toList = List.take j a2.toList ++ a2[j]?.toList)
    (h_take_succ_eq : List.take (j + 1) a2.toList = List.take j a2.toList ++ [a2[j]!])
    (h_count_take_succ : countInArray { toList := List.take (j + 1) a2.toList } v = countInArray { toList := List.take j a2.toList } v + List.count v [a2[j]!])
    (h_push_toList : True)
    (h_option_toList : a2[j]? = some a2[j]!)
    : countInArray result v + List.count v [a2[j]!] = countInArray { toList := List.take i a1.toList } v + (countInArray { toList := List.take j a2.toList } v + List.count v [a2[j]!]) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_10
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_count_inv : ∀ (v : ℕ), countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (if_pos : i < a1.size ∨ j < a2.size)
    (invariant_last_le_a1 : 0 < result.size → i < a1.size → result[result.size - 1]! ≤ a1[i]!)
    (invariant_last_le_a2 : 0 < result.size → j < a2.size → result[result.size - 1]! ≤ a2[j]!)
    (if_neg : i < a1.size)
    (if_neg_1 : j < a2.size)
    (if_neg_2 : a2[j]! < a1[i]!)
    : ∀ (v : ℕ), countInArray (result.push a2[j]!) v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take (j + 1) a2.toList } v := by
    intro v
    -- Step 1: Express countInArray of pushed array in terms of original
    have h_push_toList : (result.push a2[j]!).toList = result.toList ++ [a2[j]!] := by (try simp at *; expose_names); exact (Array.toList_push); done
    -- Step 2: countInArray of pushed array equals countInArray of result plus count of singleton
    have h_count_push : countInArray (result.push a2[j]!) v = countInArray result v + List.count v [a2[j]!] := by (try simp at *; expose_names); exact (goal_4_0 a2 a1 j i result v); done
    -- Step 3: Apply the invariant to get the count of result
    have h_inv_applied : countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v := by (try simp at *; expose_names); exact (invariant_count_inv v); done
    -- Step 4: Since j < a2.size, a2[j]? = some a2[j]!
    have h_j_lt_size : j < a2.size := by (try simp at *; expose_names); exact if_neg_1; done
    have h_getElem_some : a2[j]? = some a2[j]! := by (try simp at *; expose_names); exact (goal_10_0 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 v h_count_push h_inv_applied h_j_lt_size h_push_toList); done
    -- Step 5: Express List.take (j + 1) in terms of List.take j
    have h_take_succ : List.take (j + 1) a2.toList = List.take j a2.toList ++ a2[j]?.toList := by (try simp at *; expose_names); exact (goal_1_2 a1 a2 i j a1 i); done
    -- Step 6: a2[j]?.toList = [a2[j]!]
    have h_option_toList : a2[j]?.toList = [a2[j]!] := by (try simp at *; expose_names); exact (h_getElem_some); done
    -- Step 7: Combine to get take (j+1) = take j ++ [a2[j]!]
    have h_take_succ_eq : List.take (j + 1) a2.toList = List.take j a2.toList ++ [a2[j]!] := by (try simp at *; expose_names); exact (goal_4_2 a2 a1 j i a1 i h_getElem_some); done
    -- Step 8: Count in take (j+1) equals count in take j plus count in singleton
    have h_count_take_succ : countInArray { toList := List.take (j + 1) a2.toList } v = countInArray { toList := List.take j a2.toList } v + List.count v [a2[j]!] := by (try simp at *; expose_names); exact (goal_1_5 a1 a2 i j a1 v h_take_succ_eq); done
    -- Step 9: Chain the equalities using associativity and commutativity
    have h_rearrange : countInArray result v + List.count v [a2[j]!] = countInArray { toList := List.take i a1.toList } v + (countInArray { toList := List.take j a2.toList } v + List.count v [a2[j]!]) := by (try simp at *; expose_names); exact (goal_10_1 a1 a2 i j result if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2 v h_count_push h_inv_applied h_j_lt_size h_getElem_some h_take_succ h_take_succ_eq h_count_take_succ h_push_toList h_option_toList); done
    -- Step 10: Final equality
    calc countInArray (result.push a2[j]!) v
        = countInArray result v + List.count v [a2[j]!] := h_count_push
      _ = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v + List.count v [a2[j]!] := by (try simp at *; expose_names); exact (invariant_count_inv v); done
      _ = countInArray { toList := List.take i a1.toList } v + (countInArray { toList := List.take j a2.toList } v + List.count v [a2[j]!]) := by (try simp at *; expose_names); exact (Nat.add_assoc (countInArray { toList := List.take i a1.toList } v) (countInArray { toList := List.take j a2.toList } v) (List.count v [a2[j]!])); done
      _ = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take (j + 1) a2.toList } v := by (try simp at *; expose_names); exact (id (Eq.symm h_count_take_succ)); done

theorem goal_11
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (require_1 : precondition a1 a2)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    : j + 1 < a2.size → a2[j]! ≤ a2[j + 1]! := by
    intros; expose_names; exact (goal_2 a1 a2 require_1 i j a1 h); done

theorem goal_12
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    : isSortedArray #[] := by
    unfold isSortedArray
    intro i j h_i_lt_j h_j_lt_size
    simp [Array.size_empty] at h_j_lt_size

theorem goal_13
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    : ∀ (v : ℕ), countInArray { toList := [] } v = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_14
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (i : ℕ)
    (j : ℕ)
    (result : Array ℕ)
    (invariant_i_bound : i ≤ a1.size)
    (invariant_j_bound : j ≤ a2.size)
    (invariant_size_inv : result.size = i + j)
    (invariant_sorted_inv : isSortedArray result)
    (invariant_count_inv : ∀ (v : ℕ), countInArray result v = countInArray { toList := List.take i a1.toList } v + countInArray { toList := List.take j a2.toList } v)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (result_1 : Array ℕ)
    (a : a1.size ≤ i)
    (a_1 : a2.size ≤ j)
    (i_3 : i = i_1 ∧ j = i_2 ∧ result = result_1)
    : postcondition a1 a2 result_1 := by
    -- Extract equalities from i_3
    obtain ⟨hi, hj, hres⟩ := i_3
    -- Derive i = a1.size and j = a2.size
    have h_i_eq : i = a1.size := Nat.le_antisymm invariant_i_bound a
    have h_j_eq : j = a2.size := Nat.le_antisymm invariant_j_bound a_1
    -- Unfold postcondition
    unfold postcondition ensures1 ensures2 ensures3
    constructor
    · -- ensures1: result_1.size = a1.size + a2.size
      rw [← hres, invariant_size_inv, h_i_eq, h_j_eq]
    constructor
    · -- ensures2: isSortedArray result_1
      rw [← hres]
      exact invariant_sorted_inv
    · -- ensures3: count preservation
      intro v
      rw [← hres]
      -- Use invariant_count_inv
      have h_inv := invariant_count_inv v
      -- Since i = a1.size, List.take i a1.toList = a1.toList
      have h_take_a1 : List.take i a1.toList = a1.toList := by
        rw [h_i_eq]
        rw [← Array.length_toList]
        exact List.take_length
      -- Since j = a2.size, List.take j a2.toList = a2.toList
      have h_take_a2 : List.take j a2.toList = a2.toList := by
        rw [h_j_eq]
        rw [← Array.length_toList]
        exact List.take_length
      -- Rewrite the counts
      simp only [countInArray] at h_inv ⊢
      simp only [h_take_a1, h_take_a2] at h_inv
      exact h_inv


prove_correct mergeSorted by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a1 a2 i j result invariant_j_bound invariant_size_inv invariant_sorted_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1)
  exact (goal_1 a1 a2 i j result invariant_j_bound invariant_count_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_pos_1)
  exact (goal_2 a1 a2 require_1 i j result)
  exact (goal_3 a1 a2 i j result invariant_size_inv invariant_sorted_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_pos_1)
  exact (goal_4 a1 a2 i j result invariant_count_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_pos_1)
  exact (goal_5 a1 a2 require_1 i j result)
  exact (goal_6 a1 a2 i j result invariant_size_inv invariant_sorted_inv if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1)
  exact (goal_7 a1 a2 i j result invariant_count_inv if_pos if_pos_1 invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1)
  exact (goal_8 a1 a2 require_1 i j result)
  exact (goal_9 a1 a2 i j result invariant_size_inv invariant_sorted_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2)
  exact (goal_10 a1 a2 i j result invariant_count_inv if_pos invariant_last_le_a1 invariant_last_le_a2 if_neg if_neg_1 if_neg_2)
  exact (goal_11 a1 a2 require_1 i j result)
  exact (goal_12 a1 a2)
  exact (goal_13 a1 a2)
  exact (goal_14 a1 a2 i j result invariant_i_bound invariant_j_bound invariant_size_inv invariant_sorted_inv invariant_count_inv i_1 i_2 result_1 a a_1 i_3)
end Proof
