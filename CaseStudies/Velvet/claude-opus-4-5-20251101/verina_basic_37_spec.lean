import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- findFirstOccurrence: Find the index of the first occurrence of a target value in a sorted array
--
-- Natural language breakdown:
-- 1. We are given a sorted array of integers (non-decreasing order) and a target integer
-- 2. We need to find the index of the first occurrence of the target in the array
-- 3. If the target is not present in the array, we return -1
-- 4. The array must remain unchanged after the operation
-- 5. Key properties:
--    a. The input array must be sorted in non-decreasing order
--    b. If target exists, return the smallest index where arr[i] = target
--    c. If target does not exist, return -1
-- 6. The result uniquely identifies the first position (no earlier position has the target)

section Specs

-- Helper definition: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper definition: check if target exists in the array
def targetExists (arr : Array Int) (target : Int) : Prop :=
  ∃ i : Nat, i < arr.size ∧ arr[i]! = target

-- Precondition: array must be sorted in non-decreasing order
def precondition (arr : Array Int) (target : Int) : Prop :=
  isSortedNonDecreasing arr

-- Postcondition: result is -1 if target not found, otherwise it's the first index
def postcondition (arr : Array Int) (target : Int) (result : Int) : Prop :=
  -- Case 1: target not found, result is -1
  (¬targetExists arr target → result = -1) ∧
  -- Case 2: target found, result is a valid index with the target
  (targetExists arr target →
    result ≥ 0 ∧
    result < arr.size ∧
    arr[result.toNat]! = target ∧
    -- No earlier index contains the target (first occurrence)
    ∀ j : Nat, j < result.toNat → arr[j]! ≠ target)

end Specs

section Impl

method findFirstOccurrence (arr : Array Int) (target : Int)
  return (result : Int)
  require precondition arr target
  ensures postcondition arr target result
  do
  pure (-1)  -- placeholder

end Impl

section TestCases

-- Test case 1: Target appears multiple times, return first index
def test1_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test1_target : Int := 2
def test1_Expected : Int := 1

-- Test case 2: Target not in array
def test2_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test2_target : Int := 6
def test2_Expected : Int := -1

-- Test case 3: Target is the first element
def test3_arr : Array Int := #[1, 2, 3, 4, 5]
def test3_target : Int := 1
def test3_Expected : Int := 0

-- Test case 4: Target is the last element
def test4_arr : Array Int := #[1, 2, 3, 4, 5]
def test4_target : Int := 5
def test4_Expected : Int := 4

-- Test case 5: Target less than all elements
def test5_arr : Array Int := #[1, 2, 3, 4, 5]
def test5_target : Int := 0
def test5_Expected : Int := -1

-- Test case 6: Empty array
def test6_arr : Array Int := #[]
def test6_target : Int := 1
def test6_Expected : Int := -1

-- Test case 7: Single element array, target found
def test7_arr : Array Int := #[5]
def test7_target : Int := 5
def test7_Expected : Int := 0

-- Test case 8: Single element array, target not found
def test8_arr : Array Int := #[5]
def test8_target : Int := 3
def test8_Expected : Int := -1

-- Test case 9: All elements are the same and equal to target
def test9_arr : Array Int := #[3, 3, 3, 3]
def test9_target : Int := 3
def test9_Expected : Int := 0

-- Test case 10: Negative numbers in array
def test10_arr : Array Int := #[-5, -3, -1, 0, 2, 4]
def test10_target : Int := -3
def test10_Expected : Int := 1

-- Recommend to validate: 1, 2, 3

end TestCases
