import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- mergeSort: Sort a list of integers in ascending order using merge sort algorithm
--
-- Natural language breakdown:
-- 1. We have a list of integers as input
-- 2. The output must be a sorted list in ascending order
-- 3. The output must be a permutation of the input (same elements, possibly different order)
-- 4. Sorted means: for any two indices i < j, the element at i is less than or equal to element at j
-- 5. Permutation means: the output contains exactly the same elements as the input with the same multiplicities
-- 6. Edge cases:
--    a. Empty list returns empty list
--    b. Single element list returns the same list
--    c. List with all equal elements returns the same list
--    d. Already sorted list returns the same list
--    e. Reverse sorted list returns the reversed list
--    f. Negative numbers are handled correctly

section Specs

-- Helper function: check if a list is sorted in ascending order (non-strict)
def isSortedAsc (l : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < l.length → l[i]! ≤ l[j]!

-- Helper function: check if two lists are permutations of each other
-- Using List.Perm from Mathlib which captures that two lists have the same elements with same multiplicities
def isPermutation (l1 l2 : List Int) : Prop :=
  List.Perm l1 l2

-- Precondition: no restrictions on input
def precondition (list : List Int) : Prop :=
  True

-- Postcondition: result is sorted and is a permutation of input
def postcondition (list : List Int) (result : List Int) : Prop :=
  isSortedAsc result ∧ isPermutation list result

end Specs

section Impl

method mergeSort (list : List Int)
  return (result : List Int)
  require precondition list
  ensures postcondition list result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Example from problem - typical unsorted list
def test1_list : List Int := [5, 2, 9, 1, 5, 6]
def test1_Expected : List Int := [1, 2, 5, 5, 6, 9]

-- Test case 2: Another typical case with duplicates
def test2_list : List Int := [3, 1, 4, 1, 5, 9, 2, 6]
def test2_Expected : List Int := [1, 1, 2, 3, 4, 5, 6, 9]

-- Test case 3: Empty list (edge case)
def test3_list : List Int := []
def test3_Expected : List Int := []

-- Test case 4: Single element (edge case)
def test4_list : List Int := [1]
def test4_Expected : List Int := [1]

-- Test case 5: All equal elements
def test5_list : List Int := [5, 5, 5, 5]
def test5_Expected : List Int := [5, 5, 5, 5]

-- Test case 6: Reverse sorted list
def test6_list : List Int := [9, 8, 7, 6, 5, 4, 3, 2, 1]
def test6_Expected : List Int := [1, 2, 3, 4, 5, 6, 7, 8, 9]

-- Test case 7: Already sorted list
def test7_list : List Int := [1, 2, 3, 4, 5]
def test7_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 8: Negative numbers
def test8_list : List Int := [-3, -1, -5, -2]
def test8_Expected : List Int := [-5, -3, -2, -1]

-- Recommend to validate: 1, 3, 8

end TestCases
