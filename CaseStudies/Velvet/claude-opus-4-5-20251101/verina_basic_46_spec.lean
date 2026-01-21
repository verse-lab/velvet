import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    lastPosition: Find the last occurrence of a specified element in a sorted array of integers
    Natural language breakdown:
    1. We are given a sorted array of integers in non-decreasing order
    2. We are given an element to search for
    3. We need to find the index of the last occurrence of the element in the array
    4. If the element is not found, we return -1
    5. The array must remain unchanged after the method is executed
    6. Key properties:
       a. The array is sorted in non-decreasing order (arr[i] <= arr[j] for i < j)
       b. If result >= 0, then arr[result] = elem
       c. If result >= 0, then for all indices k > result, arr[k] != elem
       d. If result >= 0, then result is a valid index (result < arr.size)
       e. If result = -1, then elem does not appear in the array
    7. Edge cases:
       - Empty array: return -1
       - Single element array: return 0 if match, -1 otherwise
       - All elements are the same as elem: return arr.size - 1
       - Element appears multiple times: return the largest index
       - Element not in array: return -1
-/

section Specs

-- Helper definition: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition: array must be sorted in non-decreasing order
def precondition (arr : Array Int) (elem : Int) :=
  isSortedNonDecreasing arr

-- Postcondition clauses
-- Case 1: Element found - result is the last index where elem appears
def ensures_found (arr : Array Int) (elem : Int) (result : Int) :=
  result ≥ 0 →
    (result.toNat < arr.size ∧
     arr[result.toNat]! = elem ∧
     (∀ k : Nat, k < arr.size → k > result.toNat → arr[k]! ≠ elem))

-- Case 2: Element not found - result is -1 and elem does not appear in array
def ensures_not_found (arr : Array Int) (elem : Int) (result : Int) :=
  result = -1 →
    (∀ k : Nat, k < arr.size → arr[k]! ≠ elem)

-- Case 3: Result is either -1 or a valid non-negative index
def ensures_valid_result (arr : Array Int) (elem : Int) (result : Int) :=
  result = -1 ∨ (result ≥ 0 ∧ result.toNat < arr.size)

-- Case 4: If elem exists in the array, result must be non-negative
def ensures_completeness (arr : Array Int) (elem : Int) (result : Int) :=
  (∃ k : Nat, k < arr.size ∧ arr[k]! = elem) → result ≥ 0

def postcondition (arr : Array Int) (elem : Int) (result : Int) :=
  ensures_found arr elem result ∧
  ensures_not_found arr elem result ∧
  ensures_valid_result arr elem result ∧
  ensures_completeness arr elem result

end Specs

section Impl

method lastPosition (arr : Array Int) (elem : Int)
  return (result : Int)
  require precondition arr elem
  ensures postcondition arr elem result
  do
  pure (-1)  -- placeholder

end Impl

section TestCases

-- Test case 1: Element appears multiple times, find last occurrence (from problem example)
def test1_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test1_elem : Int := 2
def test1_Expected : Int := 2

-- Test case 2: Element not in array
def test2_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test2_elem : Int := 6
def test2_Expected : Int := -1

-- Test case 3: Element is the last element of array
def test3_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test3_elem : Int := 5
def test3_Expected : Int := 5

-- Test case 4: Single element array, element found
def test4_arr : Array Int := #[1]
def test4_elem : Int := 1
def test4_Expected : Int := 0

-- Test case 5: All elements are the same
def test5_arr : Array Int := #[1, 1, 1, 1]
def test5_elem : Int := 1
def test5_Expected : Int := 3

-- Test case 6: Element appears at the end of repeated sequence
def test6_arr : Array Int := #[2, 2, 3, 3, 3]
def test6_elem : Int := 3
def test6_Expected : Int := 4

-- Test case 7: Empty array
def test7_arr : Array Int := #[]
def test7_elem : Int := 5
def test7_Expected : Int := -1

-- Test case 8: Element is the first element only
def test8_arr : Array Int := #[1, 2, 3, 4, 5]
def test8_elem : Int := 1
def test8_Expected : Int := 0

-- Test case 9: Element not found, smaller than all elements
def test9_arr : Array Int := #[10, 20, 30, 40]
def test9_elem : Int := 5
def test9_Expected : Int := -1

-- Test case 10: Element appears in middle, single occurrence
def test10_arr : Array Int := #[1, 2, 3, 4, 5]
def test10_elem : Int := 3
def test10_Expected : Int := 2

-- Recommend to validate: 1, 5, 6

end TestCases
