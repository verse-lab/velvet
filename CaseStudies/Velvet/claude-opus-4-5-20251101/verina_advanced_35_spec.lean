import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    majorityElement: Find the majority element in a list of integers
    Natural language breakdown:
    1. We are given a list of integers nums with length n ≥ 1
    2. The majority element is defined as the element that appears more than ⌊n/2⌋ times
    3. We may assume that a majority element always exists in the input
    4. The result must be an element from the input list
    5. The result must have a count strictly greater than half the list length (floor division)
    6. Since a majority element exists and appears more than half the time, it is unique
    7. Edge cases:
       - Single element list: that element is the majority (appears 1 time > 0 = ⌊1/2⌋)
       - All same elements: that element is the majority
       - Mixed elements: the element appearing more than ⌊n/2⌋ times
-/

section Specs

-- Helper Functions

-- Check if an element is the majority element in a list
-- An element x is majority if it appears more than ⌊n/2⌋ times where n is the list length
def isMajority (nums : List Int) (x : Int) : Prop :=
  nums.count x > nums.length / 2

-- Precondition: list is non-empty and contains a majority element
def precondition (nums : List Int) :=
  nums.length ≥ 1 ∧ ∃ x, x ∈ nums ∧ isMajority nums x

-- Postcondition: result is in the list and is the majority element
def postcondition (nums : List Int) (result : Int) :=
  result ∈ nums ∧ isMajority nums result

end Specs

section Impl

method majorityElement (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
    pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - [3, 2, 3], majority is 3 (appears 2 times > 1)
def test1_nums : List Int := [3, 2, 3]
def test1_Expected : Int := 3

-- Test case 2: Example from problem - [2, 2, 1, 1, 1, 2, 2], majority is 2 (appears 4 times > 3)
def test2_nums : List Int := [2, 2, 1, 1, 1, 2, 2]
def test2_Expected : Int := 2

-- Test case 3: [1, 1, 1, 2, 3, 1], majority is 1 (appears 4 times > 3)
def test3_nums : List Int := [1, 1, 1, 2, 3, 1]
def test3_Expected : Int := 1

-- Test case 4: All same elements - [0, 0, 0, 0], majority is 0 (appears 4 times > 2)
def test4_nums : List Int := [0, 0, 0, 0]
def test4_Expected : Int := 0

-- Test case 5: Single element - [7], majority is 7 (appears 1 time > 0)
def test5_nums : List Int := [7]
def test5_Expected : Int := 7

-- Test case 6: Two elements same - [5, 5], majority is 5 (appears 2 times > 1)
def test6_nums : List Int := [5, 5]
def test6_Expected : Int := 5

-- Test case 7: Negative numbers - [-1, -1, -1, 2], majority is -1 (appears 3 times > 2)
def test7_nums : List Int := [-1, -1, -1, 2]
def test7_Expected : Int := -1

-- Test case 8: Large majority - [3, 3, 3, 3, 1], majority is 3 (appears 4 times > 2)
def test8_nums : List Int := [3, 3, 3, 3, 1]
def test8_Expected : Int := 3

-- Test case 9: Majority at boundaries - [1, 2, 1], majority is 1 (appears 2 times > 1)
def test9_nums : List Int := [1, 2, 1]
def test9_Expected : Int := 1

-- Test case 10: Zero as majority with negatives - [0, 0, 0, -5, 5], majority is 0 (appears 3 times > 2)
def test10_nums : List Int := [0, 0, 0, -5, 5]
def test10_Expected : Int := 0

-- Recommend to validate: 1, 2, 5

end TestCases

