import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    uniqueSorted: Given a list of integers, remove all duplicates and return the resulting list in ascending order.
    Natural language breakdown:
    1. We have an input list of integers (arr)
    2. We need to remove all duplicate elements from the list
    3. The result should contain only unique elements (no duplicates)
    4. The result should be sorted in ascending order
    5. Every element in the result must appear in the original input list
    6. Every element from the original list must appear in the result (membership preservation)
    7. Edge case: Empty list should return empty list
    8. Edge case: List with all same elements should return a single-element list
    9. The result is uniquely determined by these properties
-/

section Specs

-- Helper: Check if a list is sorted in ascending order
def isSortedAsc (lst : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < lst.length → lst[i]! ≤ lst[j]!

-- Helper: Check if a list has no duplicates (all elements are distinct)
def hasNoDuplicates (lst : List Int) : Prop :=
  ∀ i j : Nat, i < lst.length → j < lst.length → i ≠ j → lst[i]! ≠ lst[j]!

-- Postcondition clause 1: result is sorted in ascending order
def ensures1 (arr : List Int) (result : List Int) :=
  isSortedAsc result

-- Postcondition clause 2: result has no duplicates
def ensures2 (arr : List Int) (result : List Int) :=
  hasNoDuplicates result

-- Postcondition clause 3: membership preservation (element is in result iff it's in arr)
def ensures3 (arr : List Int) (result : List Int) :=
  ∀ x : Int, x ∈ result ↔ x ∈ arr

def precondition (arr : List Int) :=
  True  -- no preconditions

def postcondition (arr : List Int) (result : List Int) :=
  ensures1 arr result ∧ ensures2 arr result ∧ ensures3 arr result

end Specs

section Impl

method uniqueSorted (arr : List Int)
  return (result : List Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Basic example with duplicates (from problem description)
def test1_arr : List Int := [1, 1, 2, 3]
def test1_Expected : List Int := [1, 2, 3]

-- Test case 2: All same elements
def test2_arr : List Int := [3, 3, 3]
def test2_Expected : List Int := [3]

-- Test case 3: Empty list
def test3_arr : List Int := []
def test3_Expected : List Int := []

-- Test case 4: Unsorted with duplicates
def test4_arr : List Int := [5, 2, 2, 5]
def test4_Expected : List Int := [2, 5]

-- Test case 5: Already sorted, no duplicates
def test5_arr : List Int := [1, 2, 3, 4, 5]
def test5_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 6: Single element
def test6_arr : List Int := [42]
def test6_Expected : List Int := [42]

-- Test case 7: Negative numbers with duplicates
def test7_arr : List Int := [-3, -1, -3, 0, -1, 2]
def test7_Expected : List Int := [-3, -1, 0, 2]

-- Test case 8: Reverse sorted with no duplicates
def test8_arr : List Int := [5, 4, 3, 2, 1]
def test8_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 9: Mixed positive and negative with many duplicates
def test9_arr : List Int := [1, -1, 1, -1, 0, 0]
def test9_Expected : List Int := [-1, 0, 1]

-- Test case 10: Two elements, same value
def test10_arr : List Int := [7, 7]
def test10_Expected : List Int := [7]

-- Recommend to validate: 1, 2, 4

end TestCases
