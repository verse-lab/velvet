import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 25: Write a Velvet function to find the product of non-repeated elements in a given array
--
-- Natural language breakdown:
-- 1. Given an array of integers, we need to find all elements that appear exactly once
-- 2. An element is "non-repeated" if it appears exactly once in the array
--    (not zero times, not two or more times - exactly once)
-- 3. We need to compute the product of all such non-repeated elements
-- 4. If there are no non-repeated elements, the product should be 1 (multiplicative identity)
-- 5. The order of elements doesn't matter for the product (multiplication is commutative)
-- 6. Example: [1, 2, 3, 2] → non-repeated elements are {1, 3} → product = 1 * 3 = 3
-- 7. Example: [1, 1, 2, 2] → no non-repeated elements → product = 1
-- 8. Example: [5] → non-repeated element is {5} → product = 5
-- 9. Example: [] → no elements, no non-repeated elements → product = 1
-- 10. Example: [4, 5, 6] → all are non-repeated → product = 4 * 5 * 6 = 120
-- 11. Negative numbers and zero should be handled correctly in the product
-- 12. Multiple occurrences of the same element (appearing 2+ times) should all be excluded

-- Helper definition: count how many times a value appears in an array

section Specs

-- Helper Functions
def productOfNonRepeatedElements (arr : Array Int) : Int :=
  arr.foldl
    (fun acc x => if arr.count x = 1 then acc * x else acc)
    1

-- Postcondition clauses
def ensures1 (arr : Array Int) (product : Int) :=
  product = productOfNonRepeatedElements arr

def precondition (arr : Array Int) :=
  True  -- no preconditions
def postcondition (arr : Array Int) (product : Int) :=
  ensures1 arr product

end Specs

method ProductOfNonRepeated (arr : Array Int)
  return (product : Int)
  require precondition arr
  ensures postcondition arr product
  do
    sorry

prove_correct ProductOfNonRepeated by sorry

-- Test cases for specification validation
section TestCases

-- Test case 0: From problem description
def test0_arr : Array Int := #[1, 1, 2, 3]
def test0_Expected : Int := 6

-- Test case 1: Some repeated, some non-repeated
def test1_arr : Array Int := #[1, 2, 3, 2]
def test1_Expected : Int := 3

-- Test case 2: All repeated elements
def test2_arr : Array Int := #[1, 1, 2, 2]
def test2_Expected : Int := 1

-- Test case 3: Single element
def test3_arr : Array Int := #[5]
def test3_Expected : Int := 5

-- Test case 4: Empty array
def test4_arr : Array Int := #[]
def test4_Expected : Int := 1

-- Test case 5: All unique elements
def test5_arr : Array Int := #[4, 5, 6]
def test5_Expected : Int := 120

-- Test case 6: Array with negative numbers
def test6_arr : Array Int := #[-2, 3, -2, 4]
def test6_Expected : Int := 12

-- Test case 7: Array with zero as non-repeated element
def test7_arr : Array Int := #[0, 1, 2, 1]
def test7_Expected : Int := 0

-- Test case 8: Array with negative product
def test8_arr : Array Int := #[-3, 5, 7, 5]
def test8_Expected : Int := -21

-- Test case 9: Larger array with mixed repeated and non-repeated
def test9_arr : Array Int := #[1, 2, 3, 4, 5, 1, 2, 3]
def test9_Expected : Int := 20

-- Test case 10: Element appearing three times
def test10_arr : Array Int := #[7, 7, 7, 8, 9]
def test10_Expected : Int := 72

-- Test case 11: Large array with single non-repeated elements
def test11_arr : Array Int := #[10, 20, 30, 40, 50, 10, 20, 30, 40, 100]
def test11_Expected : Int := 5000

-- Recommend to validate: 0, 1, 4, 5, 7, 8

-- Note: All test cases verify that:
-- 1. The product equals the product of all elements appearing exactly once
-- 2. Elements appearing 0 times or 2+ times do not contribute to the product
-- 3. Empty array or array with no non-repeated elements gives product = 1
-- 4. The specification correctly handles negative numbers and zero

end TestCases
