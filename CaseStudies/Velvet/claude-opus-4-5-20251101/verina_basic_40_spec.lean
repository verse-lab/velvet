import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    secondSmallest: Find the second-smallest number in an array of integers
    Natural language breakdown:
    1. We are given an array of integers with at least two elements
    2. The array must contain at least two distinct values
    3. The second-smallest number is defined as the smallest element that is strictly greater than the minimum
    4. The result must be an element of the array
    5. The result must be strictly greater than the minimum element
    6. No element in the array can be strictly between the minimum and the result
    7. The original array remains unmodified (implicit in functional specification)
    8. Edge cases:
       - Array with exactly 2 distinct elements
       - Array with duplicates of the minimum
       - Negative numbers in the array
-/

section Specs

-- Helper Functions

-- Check if array has at least two distinct values
def hasAtLeastTwoDistinct (arr : Array Int) : Prop :=
  ∃ i j, i < arr.size ∧ j < arr.size ∧ arr[i]! ≠ arr[j]!

-- Find the minimum element in an array (for specification purposes)
def isMinimum (arr : Array Int) (m : Int) : Prop :=
  (∃ i, i < arr.size ∧ arr[i]! = m) ∧
  (∀ j, j < arr.size → arr[j]! ≥ m)

-- Check if a value is in the array
def inArray (arr : Array Int) (val : Int) : Prop :=
  ∃ i, i < arr.size ∧ arr[i]! = val

-- Precondition clauses
def require1 (s : Array Int) :=
  s.size ≥ 2  -- Array has at least two elements

def require2 (s : Array Int) :=
  hasAtLeastTwoDistinct s  -- Array has at least two distinct values

-- Postcondition clauses
-- The result is an element of the array
def ensures1 (s : Array Int) (result : Int) :=
  inArray s result

-- The result is strictly greater than the minimum
def ensures2 (s : Array Int) (result : Int) :=
  ∀ m, isMinimum s m → result > m

-- No element in the array is strictly between the minimum and the result
def ensures3 (s : Array Int) (result : Int) :=
  ∀ m, isMinimum s m →
    ∀ i, i < s.size → (s[i]! > m → s[i]! ≥ result)

def precondition (s : Array Int) :=
  require1 s ∧ require2 s

def postcondition (s : Array Int) (result : Int) :=
  ensures1 s result ∧
  ensures2 s result ∧
  ensures3 s result

end Specs

section Impl

method secondSmallest (s : Array Int)
  return (result : Int)
  require precondition s
  ensures postcondition s result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: Example from problem - mixed positive integers
def test1_s : Array Int := #[5, 3, 1, 4, 2]
def test1_Expected : Int := 2

-- Test case 2: Another example from problem
def test2_s : Array Int := #[7, 2, 5, 3]
def test2_Expected : Int := 3

-- Test case 3: Minimum size array (2 elements, ascending)
def test3_s : Array Int := #[10, 20]
def test3_Expected : Int := 20

-- Test case 4: Minimum size array (2 elements, descending)
def test4_s : Array Int := #[20, 10]
def test4_Expected : Int := 20

-- Test case 5: Small array with 3 elements
def test5_s : Array Int := #[3, 1, 2]
def test5_Expected : Int := 2

-- Test case 6: Array with negative numbers
def test6_s : Array Int := #[-5, -3, -1, -4, -2]
def test6_Expected : Int := -4

-- Test case 7: Array with duplicates of minimum
def test7_s : Array Int := #[1, 1, 1, 2, 3]
def test7_Expected : Int := 2

-- Test case 8: Array with mixed positive and negative
def test8_s : Array Int := #[-10, 0, 5, -5, 10]
def test8_Expected : Int := -5

-- Test case 9: Array with duplicates of second smallest
def test9_s : Array Int := #[1, 2, 2, 3, 4]
def test9_Expected : Int := 2

-- Test case 10: Larger array
def test10_s : Array Int := #[100, 50, 25, 75, 10, 90, 30]
def test10_Expected : Int := 25

-- Recommend to validate: 1, 3, 6

end TestCases
