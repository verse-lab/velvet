import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    mergeSortedLists: Merge two ascendingly sorted lists of integers into one sorted list
    Natural language breakdown:
    1. We have two input lists arr1 and arr2, both sorted in ascending order
    2. The result must contain all elements from both input lists
    3. The result must be sorted in ascending order
    4. The result preserves all elements (multiset equality with concatenation of inputs)
    5. Using List.Sorted from Mathlib to express sorting property
    6. The length of result equals the sum of lengths of both input lists
    7. Every element in the result appears in either arr1 or arr2
    8. The count of each element in result equals its total count in arr1 plus its count in arr2
-/

section Specs

-- Helper to check if a list is sorted in ascending order (using ≤)
def isSortedAsc (lst : List Int) : Prop :=
  List.Sorted (· ≤ ·) lst

-- Helper to count occurrences of an element in a list
def countOccurrences (x : Int) (lst : List Int) : Nat :=
  lst.filter (· == x) |>.length

-- Precondition: both input lists must be sorted in ascending order
def precondition (arr1 : List Int) (arr2 : List Int) : Prop :=
  isSortedAsc arr1 ∧ isSortedAsc arr2

-- Postcondition clauses
-- 1. The result is sorted in ascending order
def ensures1 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  isSortedAsc result

-- 2. The result has the correct length (all elements preserved)
def ensures2 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  result.length = arr1.length + arr2.length

-- 3. Every element in result comes from arr1 or arr2
def ensures3 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  ∀ x, x ∈ result → x ∈ arr1 ∨ x ∈ arr2

-- 4. Every element from arr1 and arr2 is in result (with correct multiplicity)
def ensures4 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  ∀ x, countOccurrences x result = countOccurrences x arr1 + countOccurrences x arr2

def postcondition (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  ensures1 arr1 arr2 result ∧
  ensures2 arr1 arr2 result ∧
  ensures3 arr1 arr2 result ∧
  ensures4 arr1 arr2 result

end Specs

section Impl

method mergeSortedLists (arr1 : List Int) (arr2 : List Int)
  return (result : List Int)
  require precondition arr1 arr2
  ensures postcondition arr1 arr2 result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Basic merge of two sorted lists (from problem example)
def test1_arr1 : List Int := [1, 3, 5]
def test1_arr2 : List Int := [2, 4, 6]
def test1_Expected : List Int := [1, 2, 3, 4, 5, 6]

-- Test case 2: Both empty lists
def test2_arr1 : List Int := []
def test2_arr2 : List Int := []
def test2_Expected : List Int := []

-- Test case 3: Lists with negative numbers
def test3_arr1 : List Int := [-2, 0, 1]
def test3_arr2 : List Int := [-3, -1]
def test3_Expected : List Int := [-3, -2, -1, 0, 1]

-- Test case 4: Interleaved elements
def test4_arr1 : List Int := [10, 20, 30]
def test4_arr2 : List Int := [5, 25, 35]
def test4_Expected : List Int := [5, 10, 20, 25, 30, 35]

-- Test case 5: Lists with duplicate elements
def test5_arr1 : List Int := [1, 2, 2]
def test5_arr2 : List Int := [2, 3, 3]
def test5_Expected : List Int := [1, 2, 2, 2, 3, 3]

-- Test case 6: One empty list
def test6_arr1 : List Int := [1, 2, 3]
def test6_arr2 : List Int := []
def test6_Expected : List Int := [1, 2, 3]

-- Test case 7: Other list empty
def test7_arr1 : List Int := []
def test7_arr2 : List Int := [4, 5, 6]
def test7_Expected : List Int := [4, 5, 6]

-- Test case 8: Single element lists
def test8_arr1 : List Int := [1]
def test8_arr2 : List Int := [2]
def test8_Expected : List Int := [1, 2]

-- Test case 9: All elements of arr1 less than arr2
def test9_arr1 : List Int := [1, 2, 3]
def test9_arr2 : List Int := [10, 20, 30]
def test9_Expected : List Int := [1, 2, 3, 10, 20, 30]

-- Test case 10: All elements of arr2 less than arr1
def test10_arr1 : List Int := [100, 200]
def test10_arr2 : List Int := [1, 2, 3]
def test10_Expected : List Int := [1, 2, 3, 100, 200]

-- Recommend to validate: 1, 3, 5

end TestCases
