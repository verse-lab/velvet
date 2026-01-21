import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    minArray: Find the minimum element in a non-empty array of integers

    Natural language breakdown:
    1. We are given a non-empty array of integers
    2. We need to find and return the smallest element in the array
    3. The result must satisfy two key properties:
       a. It must be less than or equal to every element in the array (minimality)
       b. It must be equal to at least one element in the array (membership/achievability)
    4. The precondition requires the array to be non-empty (size > 0)
    5. Edge cases:
       - Single element array: return that element
       - All elements equal: return that common value
       - Array with negative numbers: correctly handle negative integers
       - Array with duplicates of the minimum: still return that minimum value
-/

section Specs

-- Precondition: array must be non-empty
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: result is the minimum element
-- 1. result is less than or equal to all elements in the array
-- 2. result is equal to at least one element in the array (membership)
def postcondition (a : Array Int) (result : Int) : Prop :=
  (∀ i : Nat, i < a.size → result ≤ a[i]!) ∧
  (∃ j : Nat, j < a.size ∧ a[j]! = result)

end Specs

section Impl

method minArray (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - mixed positive integers
def test1_a : Array Int := #[5, 3, 8, 2, 7]
def test1_Expected : Int := 2

-- Test case 2: All elements are the same
def test2_a : Array Int := #[10, 10, 10]
def test2_Expected : Int := 10

-- Test case 3: Array with negative numbers
def test3_a : Array Int := #[-1, -5, 3, 0]
def test3_Expected : Int := -5

-- Test case 4: Single element array
def test4_a : Array Int := #[42]
def test4_Expected : Int := 42

-- Test case 5: Array with duplicate minimum values
def test5_a : Array Int := #[3, -2, 0, -2, 5]
def test5_Expected : Int := -2

-- Test case 6: Minimum at the beginning
def test6_a : Array Int := #[1, 5, 3, 8, 2]
def test6_Expected : Int := 1

-- Test case 7: Minimum at the end
def test7_a : Array Int := #[5, 3, 8, 2, 1]
def test7_Expected : Int := 1

-- Test case 8: Large negative numbers
def test8_a : Array Int := #[-100, -50, -200, -1]
def test8_Expected : Int := -200

-- Test case 9: Mixed positive and negative with zero
def test9_a : Array Int := #[0, -1, 1, -2, 2]
def test9_Expected : Int := -2

-- Test case 10: Two elements
def test10_a : Array Int := #[7, 3]
def test10_Expected : Int := 3

-- Recommend to validate: 1, 3, 4

end TestCases
