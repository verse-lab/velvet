import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    ToArray: Convert a list of integers into an array preserving order and elements
    Natural language breakdown:
    1. We have an input list xs of integers
    2. We need to produce an array containing all elements from xs
    3. The array must have the same size as the length of the input list
    4. Each element in the array at index i must equal the element at index i in the list
    5. The order of elements must be preserved exactly
    6. No preconditions - the method should work for any list of integers
    7. Edge case: Empty list should produce empty array
    8. Edge case: Single element list should produce single element array
-/

section Specs

-- Precondition: No requirements, any list is valid input
def precondition (xs : List Int) :=
  True

-- Postcondition: Array has same size as list length, and each element matches
def postcondition (xs : List Int) (result : Array Int) :=
  result.size = xs.length ∧
  ∀ i : Nat, i < xs.length → result[i]! = xs[i]!

end Specs

section Impl

method ToArray (xs : List Int)
  return (result : Array Int)
  require precondition xs
  ensures postcondition xs result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic list with three elements (example from problem)
def test1_xs : List Int := [1, 2, 3]
def test1_Expected : Array Int := #[1, 2, 3]

-- Test case 2: Empty list
def test2_xs : List Int := []
def test2_Expected : Array Int := #[]

-- Test case 3: List with mixed positive, negative, and zero
def test3_xs : List Int := [0, -1, 5]
def test3_Expected : Array Int := #[0, -1, 5]

-- Test case 4: Single element list
def test4_xs : List Int := [7]
def test4_Expected : Array Int := #[7]

-- Test case 5: Larger list with multiple elements
def test5_xs : List Int := [100, 200, 300, 400]
def test5_Expected : Array Int := #[100, 200, 300, 400]

-- Test case 6: List with negative numbers only
def test6_xs : List Int := [-5, -10, -15]
def test6_Expected : Array Int := #[-5, -10, -15]

-- Test case 7: List with duplicate elements
def test7_xs : List Int := [1, 1, 2, 2, 3, 3]
def test7_Expected : Array Int := #[1, 1, 2, 2, 3, 3]

-- Test case 8: List with all same elements
def test8_xs : List Int := [42, 42, 42]
def test8_Expected : Array Int := #[42, 42, 42]

-- Test case 9: List with large numbers
def test9_xs : List Int := [1000000, -999999, 0]
def test9_Expected : Array Int := #[1000000, -999999, 0]

-- Test case 10: Two element list
def test10_xs : List Int := [10, 20]
def test10_Expected : Array Int := #[10, 20]

-- Recommend to validate: 1, 2, 4

end TestCases
