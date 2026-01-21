import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    productExceptSelf: For each index i, compute the product of all elements except the one at index i
    Natural language breakdown:
    1. Given a list of integers nums, return a new list result of the same length
    2. For each index i in the input list, result[i] equals the product of all elements in nums except nums[i]
    3. Mathematically: result[i] = (product of elements before i) * (product of elements after i)
    4. The solution must work without using division (important for handling zeros)
    5. Example: [1,2,3,4] → [2*3*4, 1*3*4, 1*2*4, 1*2*3] = [24, 12, 8, 6]
    6. Edge cases:
       - List with zeros: product except the zero position may be non-zero
       - Multiple zeros: all positions will be zero except possibly none
       - Two-element list: each element becomes the other
       - Negative numbers: signs must be handled correctly
    7. The result list has the same length as the input list
    8. For empty list, result is empty list
    9. For single-element list [x], result is [1] (product of empty set is 1)
-/

section Specs

-- Helper function: product of a list of integers using fold
def listProduct (lst : List Int) : Int :=
  lst.foldl (· * ·) 1

-- Precondition: no specific constraints, accept any list
def precondition (nums : List Int) :=
  True

-- Postcondition: 
-- 1. Result has the same length as input
-- 2. For each index i, result[i] equals the product of prefix (elements before i) times suffix (elements after i)
def postcondition (nums : List Int) (result : List Int) :=
  result.length = nums.length ∧
  ∀ i : Nat, i < nums.length → 
    result[i]! = listProduct (nums.take i) * listProduct (nums.drop (i + 1))

end Specs

section Impl

method productExceptSelf (nums : List Int)
  return (result : List Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Example from problem description [1,2,3,4] → [24,12,8,6]
def test1_nums : List Int := [1, 2, 3, 4]
def test1_Expected : List Int := [24, 12, 8, 6]

-- Test case 2: List with zero [-1,1,0,-3,3] → [0,0,9,0,0]
def test2_nums : List Int := [-1, 1, 0, -3, 3]
def test2_Expected : List Int := [0, 0, 9, 0, 0]

-- Test case 3: Two-element list [2,3] → [3,2]
def test3_nums : List Int := [2, 3]
def test3_Expected : List Int := [3, 2]

-- Test case 4: All same elements [5,5,5,5] → [125,125,125,125]
def test4_nums : List Int := [5, 5, 5, 5]
def test4_Expected : List Int := [125, 125, 125, 125]

-- Test case 5: Zero at beginning [0,1,2] → [2,0,0]
def test5_nums : List Int := [0, 1, 2]
def test5_Expected : List Int := [2, 0, 0]

-- Test case 6: Single element [7] → [1] (product of empty set)
def test6_nums : List Int := [7]
def test6_Expected : List Int := [1]

-- Test case 7: Empty list [] → []
def test7_nums : List Int := []
def test7_Expected : List Int := []

-- Test case 8: Negative numbers [-2, -3, 4] → [-12, -8, 6]
def test8_nums : List Int := [-2, -3, 4]
def test8_Expected : List Int := [-12, -8, 6]

-- Test case 9: Multiple zeros [0, 0, 2] → [0, 0, 0]
def test9_nums : List Int := [0, 0, 2]
def test9_Expected : List Int := [0, 0, 0]

-- Test case 10: Alternating signs [1, -1, 1, -1] → [1, -1, 1, -1]
def test10_nums : List Int := [1, -1, 1, -1]
def test10_Expected : List Int := [1, -1, 1, -1]

-- Recommend to validate: 1, 2, 3

end TestCases
