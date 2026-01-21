import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- insertionSort: Sort a list of integers in ascending order using insertion sort
--
-- Natural language breakdown:
-- 1. The input is a list of integers that may be in any order
-- 2. The output must be a sorted list in non-decreasing order (ascending)
-- 3. The output must be a permutation of the input (same elements, possibly reordered)
-- 4. Sorted means: for all adjacent elements, the earlier one is ≤ the later one
-- 5. Permutation means: the output contains exactly the same elements with the same multiplicities
-- 6. We use List.Sorted from Mathlib which defines sortedness via Pairwise relation
-- 7. We use List.Perm from Lean/Mathlib to express permutation property

section Specs

-- Precondition: No restrictions on input list
def precondition (l : List Int) : Prop :=
  True

-- Postcondition: Result is sorted and is a permutation of input
-- Using Mathlib's List.Sorted for sortedness property
-- Using List.Perm for permutation property
def postcondition (l : List Int) (result : List Int) : Prop :=
  List.Sorted (· ≤ ·) result ∧ List.Perm l result

end Specs

section Impl

method insertionSort (l : List Int)
  return (result : List Int)
  require precondition l
  ensures postcondition l result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Empty list
def test1_l : List Int := []
def test1_Expected : List Int := []

-- Test case 2: Single element list
def test2_l : List Int := [5]
def test2_Expected : List Int := [5]

-- Test case 3: Already sorted list
def test3_l : List Int := [1, 2, 3]
def test3_Expected : List Int := [1, 2, 3]

-- Test case 4: Reverse sorted list
def test4_l : List Int := [3, 2, 1]
def test4_Expected : List Int := [1, 2, 3]

-- Test case 5: List with duplicates
def test5_l : List Int := [4, 2, 2, 3]
def test5_Expected : List Int := [2, 2, 3, 4]

-- Test case 6: List with negative numbers
def test6_l : List Int := [3, -1, 4, -5, 2]
def test6_Expected : List Int := [-5, -1, 2, 3, 4]

-- Test case 7: List with all same elements
def test7_l : List Int := [7, 7, 7, 7]
def test7_Expected : List Int := [7, 7, 7, 7]

-- Test case 8: Two elements in wrong order
def test8_l : List Int := [10, 5]
def test8_Expected : List Int := [5, 10]

-- Test case 9: Longer list with mixed values
def test9_l : List Int := [5, 2, 8, 1, 9, 3]
def test9_Expected : List Int := [1, 2, 3, 5, 8, 9]

-- Recommend to validate: 1, 4, 5

end TestCases
