import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    differenceMinMax: Calculate the difference between maximum and minimum values in an array
    Natural language breakdown:
    1. We have an array of integers as input
    2. We need to find the maximum value in the array
    3. We need to find the minimum value in the array
    4. The result is the difference: maximum - minimum
    5. The array must be non-empty (precondition)
    6. Key properties:
       - The result must equal max - min where max is the largest element and min is the smallest
       - For a single element array, the result is 0 (max = min)
       - For arrays with all identical elements, the result is 0
       - The result is always non-negative (max >= min by definition)
    7. This is a property-oriented specification: we specify what properties the result must satisfy
-/

section Specs

-- Helper definition: check if a value is the maximum in the array
def isMaximum (arr : Array Int) (val : Int) : Prop :=
  (∃ i : Nat, i < arr.size ∧ arr[i]! = val) ∧
  (∀ j : Nat, j < arr.size → arr[j]! ≤ val)

-- Helper definition: check if a value is the minimum in the array
def isMinimum (arr : Array Int) (val : Int) : Prop :=
  (∃ i : Nat, i < arr.size ∧ arr[i]! = val) ∧
  (∀ j : Nat, j < arr.size → arr[j]! ≥ val)

-- Precondition: array must be non-empty
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: result is max - min
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (maxVal : Int) (minVal : Int),
    isMaximum a maxVal ∧
    isMinimum a minVal ∧
    result = maxVal - minVal

end Specs

section Impl

method differenceMinMax (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Mixed positive integers
def test1_a : Array Int := #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
def test1_Expected : Int := 8  -- max=9, min=1, diff=8

-- Test case 2: Ascending sequence
def test2_a : Array Int := #[10, 20, 30, 40, 50]
def test2_Expected : Int := 40  -- max=50, min=10, diff=40

-- Test case 3: All negative numbers
def test3_a : Array Int := #[-10, -20, -30, -40, -50]
def test3_Expected : Int := 40  -- max=-10, min=-50, diff=40

-- Test case 4: Single element array
def test4_a : Array Int := #[7]
def test4_Expected : Int := 0  -- max=min=7, diff=0

-- Test case 5: All identical elements
def test5_a : Array Int := #[5, 5, 5, 5]
def test5_Expected : Int := 0  -- max=min=5, diff=0

-- Test case 6: Mixed positive and negative
def test6_a : Array Int := #[1, -1, 2, -2]
def test6_Expected : Int := 4  -- max=2, min=-2, diff=4

-- Test case 7: Two elements
def test7_a : Array Int := #[100, -100]
def test7_Expected : Int := 200  -- max=100, min=-100, diff=200

-- Test case 8: Descending sequence
def test8_a : Array Int := #[50, 40, 30, 20, 10]
def test8_Expected : Int := 40  -- max=50, min=10, diff=40

-- Test case 9: Zero included
def test9_a : Array Int := #[0, 5, -5, 10]
def test9_Expected : Int := 15  -- max=10, min=-5, diff=15

-- Recommend to validate: 1, 3, 4

end TestCases
