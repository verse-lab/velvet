import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- MoveZeroesToEnd: Rearrange an array of integers by moving all zeros to the end
--
-- Natural language breakdown:
-- 1. Given an array of integers, we need to move all zero values to the end
-- 2. The relative order of non-zero elements must be preserved
-- 3. The length of the result array must equal the length of the input array
-- 4. The count of zeros in the result must equal the count of zeros in the input
-- 5. The non-zero elements in the result (in order) must match the non-zero elements in the input (in order)
-- 6. All zeros in the result must appear after all non-zero elements
-- 7. Example: [0, 1, 0, 3, 12] -> [1, 3, 12, 0, 0]
--    - Non-zero elements [1, 3, 12] preserve their relative order
--    - Two zeros are moved to the end
-- 8. Edge cases:
--    - Empty array: returns empty array
--    - All zeros: returns all zeros (unchanged)
--    - No zeros: returns the same array (unchanged)

section Specs

-- Helper: extract non-zero elements preserving order
def nonZeroElements (arr : Array Int) : List Int :=
  (arr.toList).filter (· ≠ 0)

-- Helper: count zeros in an array
def countZeros (arr : Array Int) : Nat :=
  arr.toList.count 0

-- Helper: check if all elements from index i onwards are zero
def allZerosFrom (arr : Array Int) (i : Nat) : Prop :=
  ∀ j : Nat, i ≤ j → j < arr.size → arr[j]! = 0

-- Helper: check if all elements before index i are non-zero
def allNonZerosBefore (arr : Array Int) (i : Nat) : Prop :=
  ∀ j : Nat, j < i → j < arr.size → arr[j]! ≠ 0

-- Precondition: no restrictions on input
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: characterizes the result
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  -- Length is preserved
  result.size = arr.size ∧
  -- The count of zeros is preserved
  countZeros result = countZeros arr ∧
  -- Non-zero elements preserve their relative order
  nonZeroElements result = nonZeroElements arr ∧
  -- There exists a boundary index such that:
  -- all elements before it are non-zero and all elements from it onwards are zero
  (∃ k : Nat, k ≤ result.size ∧ allNonZerosBefore result k ∧ allZerosFrom result k)

end Specs

section Impl

method MoveZeroesToEnd (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Example from problem - mixed zeros and non-zeros
def test1_arr : Array Int := #[0, 1, 0, 3, 12]
def test1_Expected : Array Int := #[1, 3, 12, 0, 0]

-- Test case 2: Zeros at the beginning
def test2_arr : Array Int := #[0, 0, 1]
def test2_Expected : Array Int := #[1, 0, 0]

-- Test case 3: No zeros (already valid)
def test3_arr : Array Int := #[1, 2, 3]
def test3_Expected : Array Int := #[1, 2, 3]

-- Test case 4: All zeros (no change needed)
def test4_arr : Array Int := #[0, 0, 0]
def test4_Expected : Array Int := #[0, 0, 0]

-- Test case 5: Empty array
def test5_arr : Array Int := #[]
def test5_Expected : Array Int := #[]

-- Test case 6: Single non-zero element
def test6_arr : Array Int := #[5]
def test6_Expected : Array Int := #[5]

-- Test case 7: Single zero element
def test7_arr : Array Int := #[0]
def test7_Expected : Array Int := #[0]

-- Test case 8: Negative numbers with zeros
def test8_arr : Array Int := #[-1, 0, -2, 0, -3]
def test8_Expected : Array Int := #[-1, -2, -3, 0, 0]

-- Test case 9: Zero at the end (already valid position)
def test9_arr : Array Int := #[1, 2, 0]
def test9_Expected : Array Int := #[1, 2, 0]

-- Test case 10: Alternating zeros and non-zeros
def test10_arr : Array Int := #[0, 1, 0, 2, 0, 3]
def test10_Expected : Array Int := #[1, 2, 3, 0, 0, 0]

-- Recommend to validate: 1, 2, 5

end TestCases
