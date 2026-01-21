import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    insertionSort: Sort a list of integers using insertion sort algorithm
    Natural language breakdown:
    1. We have an input list of integers
    2. The output must be a sorted list in ascending order
    3. The output must be a permutation of the input (contain exactly the same elements)
    4. The algorithm should follow insertion sort approach (placing each element in correct position)
    5. Edge cases: empty list returns empty list, single element list returns itself
    6. Duplicate elements should be preserved
    7. Negative numbers should be handled correctly
-/

section Specs

-- Helper function to check if a list is sorted in ascending order
-- Using List.Sorted from Mathlib with (· ≤ ·) relation
def isSortedAsc (xs : List Int) : Prop :=
  List.Sorted (· ≤ ·) xs

-- Helper function to check if two lists are permutations of each other
-- Using List.Perm from Mathlib (explicit form instead of ~ notation)
def isPermOf (xs : List Int) (ys : List Int) : Prop :=
  List.Perm xs ys

-- Precondition: no constraints on input
def precondition (xs : List Int) : Prop :=
  True

-- Postcondition: result is sorted and is a permutation of input
def postcondition (xs : List Int) (result : List Int) : Prop :=
  isSortedAsc result ∧ isPermOf result xs

end Specs

section Impl

method insertionSort (xs : List Int)
  return (result : List Int)
  require precondition xs
  ensures postcondition xs result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Example from problem description
def test1_xs : List Int := [3, 1, 4, 2]
def test1_Expected : List Int := [1, 2, 3, 4]

-- Test case 2: Empty list
def test2_xs : List Int := []
def test2_Expected : List Int := []

-- Test case 3: Single element
def test3_xs : List Int := [42]
def test3_Expected : List Int := [42]

-- Test case 4: List with negative numbers and duplicates
def test4_xs : List Int := [5, -1, 0, 10, -1]
def test4_Expected : List Int := [-1, -1, 0, 5, 10]

-- Test case 5: All elements are the same
def test5_xs : List Int := [2, 2, 2, 2, 2]
def test5_Expected : List Int := [2, 2, 2, 2, 2]

-- Test case 6: Already sorted list
def test6_xs : List Int := [1, 2, 3, 4, 5]
def test6_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 7: Reverse sorted list
def test7_xs : List Int := [5, 4, 3, 2, 1]
def test7_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 8: List with two elements
def test8_xs : List Int := [7, 3]
def test8_Expected : List Int := [3, 7]

-- Recommend to validate: 1, 2, 4

end TestCases
