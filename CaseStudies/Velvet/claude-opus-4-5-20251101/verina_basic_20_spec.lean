import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    uniqueProduct: Calculate the product of all distinct integers in an array
    Natural language breakdown:
    1. Given an array of integers, we need to find all unique (distinct) integers
    2. Each unique integer should be counted only once regardless of how many times it appears
    3. We compute the product of all these distinct integers
    4. If the array is empty, the result should be 1 (multiplicative identity)
    5. The order of multiplication does not affect the result (multiplication is commutative)
    6. Example: [2, 3, 2, 4] has distinct elements {2, 3, 4}, product = 2 * 3 * 4 = 24
    7. Example: [5, 5, 5, 5] has distinct element {5}, product = 5
    8. Example: [] has no elements, product = 1
    9. If any distinct element is 0, the product will be 0
    10. Negative numbers should be handled correctly in the product
-/

section Specs

-- Property-based specification:
-- The result is the product of some list of distinct elements where:
-- 1. Every element in that list appears in the original array
-- 2. Every element in the original array appears in that list
-- 3. The list has no duplicates
-- Since multiplication is commutative and associative, the product is unique

def precondition (arr : Array Int) :=
  True  -- no preconditions needed

def postcondition (arr : Array Int) (result : Int) :=
  ∃ distinctList : List Int,
    (∀ x, x ∈ distinctList ↔ x ∈ arr.toList) ∧
    distinctList.Nodup ∧
    result = distinctList.prod

end Specs

section Impl

method uniqueProduct (arr : Array Int)
  return (result : Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure 1  -- placeholder

end Impl

section TestCases

-- Test case 1: Array with duplicates [2, 3, 2, 4] (example from problem)
-- Distinct elements: {2, 3, 4}, product = 2 * 3 * 4 = 24
def test1_arr : Array Int := #[2, 3, 2, 4]
def test1_Expected : Int := 24

-- Test case 2: Array with all same elements [5, 5, 5, 5]
-- Distinct element: {5}, product = 5
def test2_arr : Array Int := #[5, 5, 5, 5]
def test2_Expected : Int := 5

-- Test case 3: Empty array []
-- No elements, product = 1 (identity)
def test3_arr : Array Int := #[]
def test3_Expected : Int := 1

-- Test case 4: Array with all distinct elements [1, 2, 3]
-- Distinct elements: {1, 2, 3}, product = 1 * 2 * 3 = 6
def test4_arr : Array Int := #[1, 2, 3]
def test4_Expected : Int := 6

-- Test case 5: Array containing zero [0, 2, 3]
-- Distinct elements: {0, 2, 3}, product = 0 * 2 * 3 = 0
def test5_arr : Array Int := #[0, 2, 3]
def test5_Expected : Int := 0

-- Test case 6: Array with negative numbers and duplicates [-1, -2, -1, -3]
-- Distinct elements: {-1, -2, -3}, product = (-1) * (-2) * (-3) = -6
def test6_arr : Array Int := #[-1, -2, -1, -3]
def test6_Expected : Int := -6

-- Test case 7: Array with multiple duplicates [10, 10, 20, 20, 30]
-- Distinct elements: {10, 20, 30}, product = 10 * 20 * 30 = 6000
def test7_arr : Array Int := #[10, 10, 20, 20, 30]
def test7_Expected : Int := 6000

-- Test case 8: Single element array [7]
-- Distinct element: {7}, product = 7
def test8_arr : Array Int := #[7]
def test8_Expected : Int := 7

-- Test case 9: Array with positive and negative duplicates [-2, 3, -2, 3, 5]
-- Distinct elements: {-2, 3, 5}, product = (-2) * 3 * 5 = -30
def test9_arr : Array Int := #[-2, 3, -2, 3, 5]
def test9_Expected : Int := -30

-- Test case 10: Array with 1 and duplicates [1, 1, 2, 2, 3]
-- Distinct elements: {1, 2, 3}, product = 1 * 2 * 3 = 6
def test10_arr : Array Int := #[1, 1, 2, 2, 3]
def test10_Expected : Int := 6

-- Recommend to validate: 1, 3, 6

end TestCases
