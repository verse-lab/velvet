import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    arraySum: Calculate the sum of all elements in an array of integers
    Natural language breakdown:
    1. We are given an array of integers (can include positive, negative, or zero values)
    2. We need to compute the sum of all elements in the array
    3. The result is a single integer representing the total sum
    4. Key properties:
       - The sum of elements should equal the result
       - For arrays with mixed positive and negative numbers, they should cancel appropriately
       - The operation is well-defined for any non-empty array
    5. Edge cases:
       - Array with single element: sum equals that element
       - Array with positive and negative numbers that cancel: sum is 0
       - Array with all negative numbers: sum is negative
    6. Based on reject inputs, empty arrays should be excluded via precondition
-/

section Specs

-- Using Array.sum from Mathlib/Init which computes sum via foldr (· + ·) 0

-- Precondition: array must be non-empty (based on reject inputs)
def precondition (a : Array Int) :=
  a.size > 0

-- Postcondition: result equals the sum of all array elements
-- Using index-based specification to describe the relationship
def postcondition (a : Array Int) (result : Int) :=
  result = a.toList.sum

end Specs

section Impl

method arraySum (a: Array Int)
  return (result: Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Basic array with positive integers (from problem description)
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Int := 15

-- Test case 2: Array with larger positive integers
def test2_a : Array Int := #[13, 14, 15, 16, 17]
def test2_Expected : Int := 75

-- Test case 3: Array with all negative integers
def test3_a : Array Int := #[-1, -2, -3]
def test3_Expected : Int := -6

-- Test case 4: Array with positive and negative integers that cancel
def test4_a : Array Int := #[10, -10]
def test4_Expected : Int := 0

-- Test case 5: Single element array
def test5_a : Array Int := #[42]
def test5_Expected : Int := 42

-- Test case 6: Array with zeros
def test6_a : Array Int := #[0, 0, 0, 5]
def test6_Expected : Int := 5

-- Test case 7: Array with mixed positive, negative, and zero
def test7_a : Array Int := #[-5, 0, 5, 10, -10]
def test7_Expected : Int := 0

-- Test case 8: Array with large numbers
def test8_a : Array Int := #[100, 200, 300]
def test8_Expected : Int := 600

-- Test case 9: Single negative element
def test9_a : Array Int := #[-99]
def test9_Expected : Int := -99

-- Test case 10: Array summing to negative
def test10_a : Array Int := #[1, -5, 2, -3]
def test10_Expected : Int := -5

-- Recommend to validate: 1, 3, 4

end TestCases

