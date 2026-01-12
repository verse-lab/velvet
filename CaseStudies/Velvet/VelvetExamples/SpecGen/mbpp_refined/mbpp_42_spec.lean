import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    SumOfRepeatedElements: Find the sum of repeated elements in a given array
    Natural language breakdown:
    1. We are given an array of integers
    2. An element is "repeated" if it appears more than once in the array (at least 2 times)
    3. For each element that appears multiple times, we include ALL its occurrences in the sum
    4. Elements that appear exactly once do NOT contribute to the sum
    5. Example: [1,2,3,1,1,4,5,6] → element 1 appears 3 times (which is > 1), so sum = 1+1+1 = 3
    6. Example: [1,2,3,1,2] → element 1 appears 2 times, element 2 appears 2 times, so sum = 1+1+2+2 = 6
    7. Example: [1,2,3,4] → no repeated elements, so sum = 0
    8. Example: [5,5,5,5] → element 5 appears 4 times, so sum = 5+5+5+5 = 20
    9. The sum is the total of all occurrences of values that appear at least twice
    10. Edge cases:
        - Empty array: sum = 0
        - All unique elements: sum = 0
        - All same elements: sum = value * count
        - Mixed repeated and non-repeated: only sum the repeated ones
-/

-- Helper Functions

-- Count how many times a value appears in an array

section Specs

-- Helper Functions

def isRepeated (arr : Array Int) (value : Int) : Bool :=
  arr.count value > 1

def sumOfRepeatedElements (arr : Array Int) : Int :=
  arr.foldl
  (fun acc x => if isRepeated arr x then acc + x else acc) 0

-- Postcondition clauses
def ensures1 (arr : Array Int) (sum : Int) :=
  sum = sumOfRepeatedElements arr

def precondition (arr : Array Int) :=
  True  -- no preconditions
def postcondition (arr : Array Int) (sum : Int) :=
  ensures1 arr sum

end Specs

method SumOfRepeated (arr: Array Int)
  return (sum: Int)
  require precondition arr
  ensures postcondition arr sum
  do
    sorry

prove_correct SumOfRepeated by sorry

section TestCases

-- Test case 1: From problem statement (MUST be first)
def test1_arr : Array Int := #[1, 2, 3, 1, 1, 4, 5, 6]
def test1_Expected : Int := 3

-- Test case 2: Multiple different repeated elements
def test2_arr : Array Int := #[1, 2, 3, 1, 2]
def test2_Expected : Int := 6

-- Test case 3: No repeated elements
def test3_arr : Array Int := #[1, 2, 3, 4]
def test3_Expected : Int := 0

-- Test case 4: All same elements
def test4_arr : Array Int := #[5, 5, 5, 5]
def test4_Expected : Int := 20

-- Test case 5: Empty array
def test5_arr : Array Int := #[]
def test5_Expected : Int := 0

-- Test case 6: Single element (no repetition)
def test6_arr : Array Int := #[7]
def test6_Expected : Int := 0

-- Test case 7: Two elements, both repeated
def test7_arr : Array Int := #[3, 3, 4, 4]
def test7_Expected : Int := 14

-- Test case 8: Mix of repeated and non-repeated with negative numbers
def test8_arr : Array Int := #[-1, 2, -1, 3, 4, 2]
def test8_Expected : Int := 2

-- Test case 9: Element appearing many times
def test9_arr : Array Int := #[2, 2, 2, 2, 2]
def test9_Expected : Int := 10

-- Test case 10: Large array with multiple repeated values
def test10_arr : Array Int := #[1, 2, 3, 4, 5, 1, 2, 3, 4, 10]
def test10_Expected : Int := 20

-- Test case 11: Array with zeros
def test11_arr : Array Int := #[0, 1, 0, 2, 3]
def test11_Expected : Int := 0

-- Test case 12: Repeated negative numbers
def test12_arr : Array Int := #[-5, -3, -5, -3, 1]
def test12_Expected : Int := -16

-- Recommend to validate: test cases 1, 2, 3, 4, 5, 8
-- These cover:
-- - Test 1: Problem statement example (required)
-- - Test 2: Multiple different repeated elements
-- - Test 3: No repeated elements edge case
-- - Test 4: All identical elements
-- - Test 5: Empty array edge case
-- - Test 8: Mix with negative numbers

end TestCases
