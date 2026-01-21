import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    remove_front: Remove the first element from an array of integers
    Natural language breakdown:
    1. We are given an array of integers
    2. The array must be non-empty (has at least one element)
    3. We need to return a new array that excludes the first element
    4. The resulting array has length equal to the original length minus one
    5. For every index i in the result, result[i] equals input[i+1]
    6. Edge case: Single element array returns empty array
-/

section Specs

-- Precondition: Array must be non-empty
def precondition (a : Array Int) :=
  a.size > 0

-- Postcondition: Result is the array without the first element
-- 1. Length is one less than original
-- 2. Each element at index i in result equals element at index i+1 in original
def postcondition (a : Array Int) (result : Array Int) :=
  result.size = a.size - 1 ∧
  ∀ i : Nat, i < result.size → result[i]! = a[i + 1]!

end Specs

section Impl

method remove_front (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Standard array with 5 elements
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Array Int := #[2, 3, 4, 5]

-- Test case 2: Array with 3 elements
def test2_a : Array Int := #[10, 20, 30]
def test2_Expected : Array Int := #[20, 30]

-- Test case 3: Array with negative numbers
def test3_a : Array Int := #[0, -1, -2, -3]
def test3_Expected : Array Int := #[-1, -2, -3]

-- Test case 4: Single element array (edge case - returns empty)
def test4_a : Array Int := #[7]
def test4_Expected : Array Int := #[]

-- Test case 5: Mixed values
def test5_a : Array Int := #[100, 0, 50]
def test5_Expected : Array Int := #[0, 50]

-- Test case 6: Two elements
def test6_a : Array Int := #[42, 99]
def test6_Expected : Array Int := #[99]

-- Test case 7: Array with all same values
def test7_a : Array Int := #[5, 5, 5, 5]
def test7_Expected : Array Int := #[5, 5, 5]

-- Test case 8: Large positive and negative values
def test8_a : Array Int := #[1000000, -1000000, 0]
def test8_Expected : Array Int := #[-1000000, 0]

-- Test case 9: Descending sequence
def test9_a : Array Int := #[9, 8, 7, 6, 5, 4, 3, 2, 1]
def test9_Expected : Array Int := #[8, 7, 6, 5, 4, 3, 2, 1]

-- Test case 10: Array starting with zero
def test10_a : Array Int := #[0, 1, 2]
def test10_Expected : Array Int := #[1, 2]

-- Recommend to validate: 1, 4, 3

end TestCases
