import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    mergeSorted: Merge two sorted integer lists into a single sorted list
    Natural language breakdown:
    1. We have two input lists a and b, both containing integers
    2. Both input lists are sorted in non-decreasing order (precondition)
    3. The result must contain all elements from both input lists
    4. The result must be sorted in non-decreasing order
    5. The result is a permutation of the concatenation of a and b
    6. Edge case: If one list is empty, result is the other list
    7. Edge case: If both lists are empty, result is empty
    8. Duplicate elements should be preserved in the output
-/

section Specs

-- Helper function to check if a list of integers is sorted in non-decreasing order
def isSortedInt (lst : List Int) : Prop :=
  ∀ i : Nat, i + 1 < lst.length → lst[i]! ≤ lst[i + 1]!

-- Precondition: both input lists must be sorted in non-decreasing order
def precondition (a : List Int) (b : List Int) : Prop :=
  isSortedInt a ∧ isSortedInt b

-- Postcondition clause 1: result is sorted in non-decreasing order
def ensures1 (a : List Int) (b : List Int) (result : List Int) : Prop :=
  isSortedInt result

-- Postcondition clause 2: result is a permutation of the concatenation of a and b
-- This ensures all elements from both lists are in the result with correct multiplicity
def ensures2 (a : List Int) (b : List Int) (result : List Int) : Prop :=
  result.Perm (a ++ b)

-- Combined postcondition
def postcondition (a : List Int) (b : List Int) (result : List Int) : Prop :=
  ensures1 a b result ∧ ensures2 a b result

end Specs

section Impl

method mergeSorted (a : List Int) (b : List Int)
  return (result : List Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Basic interleaving of two sorted lists (from problem description)
def test1_a : List Int := [1, 3, 5]
def test1_b : List Int := [2, 4, 6]
def test1_Expected : List Int := [1, 2, 3, 4, 5, 6]

-- Test case 2: Lists with duplicate elements
def test2_a : List Int := [1, 2]
def test2_b : List Int := [1, 2, 3]
def test2_Expected : List Int := [1, 1, 2, 2, 3]

-- Test case 3: First list is empty
def test3_a : List Int := []
def test3_b : List Int := [4, 5]
def test3_Expected : List Int := [4, 5]

-- Test case 4: Second list is empty
def test4_a : List Int := [0, 3, 4]
def test4_b : List Int := []
def test4_Expected : List Int := [0, 3, 4]

-- Test case 5: Alternating merge
def test5_a : List Int := [1, 4, 6]
def test5_b : List Int := [2, 3, 5]
def test5_Expected : List Int := [1, 2, 3, 4, 5, 6]

-- Test case 6: Both lists empty
def test6_a : List Int := []
def test6_b : List Int := []
def test6_Expected : List Int := []

-- Test case 7: Single element lists
def test7_a : List Int := [5]
def test7_b : List Int := [3]
def test7_Expected : List Int := [3, 5]

-- Test case 8: Lists with negative integers
def test8_a : List Int := [-5, -2, 0]
def test8_b : List Int := [-3, 1, 4]
def test8_Expected : List Int := [-5, -3, -2, 0, 1, 4]

-- Test case 9: All elements from first list come before second
def test9_a : List Int := [1, 2, 3]
def test9_b : List Int := [10, 20, 30]
def test9_Expected : List Int := [1, 2, 3, 10, 20, 30]

-- Test case 10: Lists with all same elements
def test10_a : List Int := [2, 2, 2]
def test10_b : List Int := [2, 2]
def test10_Expected : List Int := [2, 2, 2, 2, 2]

-- Recommend to validate: 1, 2, 5

end TestCases
