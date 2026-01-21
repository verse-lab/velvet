import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    maxArray: Find the maximum value in a non-empty array of integers
    Natural language breakdown:
    1. We have a non-empty array of integers as input
    2. We need to find the maximum element in the array
    3. The result must be greater than or equal to every element in the array (maximality)
    4. The result must be equal to at least one element in the array (achievability/membership)
    5. Edge cases:
       - Single element array: the element is the maximum
       - All negative numbers: the largest (closest to zero) is the maximum
       - Array with duplicates: the maximum value is still well-defined
    6. Precondition: The array must be non-empty (size >= 1)
-/

section Specs

-- Helper: Check if a value is in the array
def inArray (a : Array Int) (val : Int) : Prop :=
  ∃ i : Nat, i < a.size ∧ a[i]! = val

-- Helper: Check if a value is greater than or equal to all elements
def isMaximal (a : Array Int) (val : Int) : Prop :=
  ∀ i : Nat, i < a.size → a[i]! ≤ val

-- Precondition: Array must be non-empty
def precondition (a : Array Int) : Prop :=
  a.size ≥ 1

-- Postcondition: Result is the maximum element
-- 1. Result is greater than or equal to all elements (maximality)
-- 2. Result is an element of the array (achievability)
def postcondition (a : Array Int) (result : Int) : Prop :=
  isMaximal a result ∧ inArray a result

end Specs

section Impl

method maxArray (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Ascending sorted array
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Int := 5

-- Test case 2: Unsorted array with max at beginning
def test2_a : Array Int := #[5, 3, 4, 1, 2]
def test2_Expected : Int := 5

-- Test case 3: Single element array
def test3_a : Array Int := #[7]
def test3_Expected : Int := 7

-- Test case 4: All negative numbers
def test4_a : Array Int := #[-1, -5, -3, -4]
def test4_Expected : Int := -1

-- Test case 5: Negative numbers with max in middle
def test5_a : Array Int := #[-10, -20, -30, -5, -15]
def test5_Expected : Int := -5

-- Test case 6: Array with duplicate maximum values
def test6_a : Array Int := #[3, 5, 5, 2, 5]
def test6_Expected : Int := 5

-- Test case 7: Descending sorted array
def test7_a : Array Int := #[10, 8, 6, 4, 2]
def test7_Expected : Int := 10

-- Test case 8: Array with all same elements
def test8_a : Array Int := #[4, 4, 4, 4]
def test8_Expected : Int := 4

-- Test case 9: Mixed positive and negative numbers
def test9_a : Array Int := #[-5, 0, 3, -2, 7, 1]
def test9_Expected : Int := 7

-- Test case 10: Two elements
def test10_a : Array Int := #[100, -100]
def test10_Expected : Int := 100

-- Recommend to validate: 1, 3, 4

end TestCases
