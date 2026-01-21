import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    majorityElement: Return the majority element from a list of integers
    Natural language breakdown:
    1. The majority element is defined as the element that appears more than ⌊n / 2⌋ times,
       where n is the length of the list
    2. The input list is guaranteed to have at least one element (non-empty)
    3. The input list is guaranteed to contain a majority element
    4. The result must be an element that exists in the input list
    5. The result must have a count strictly greater than half the list length (floor division)
    6. Since a majority element exists and is unique (by pigeonhole principle), 
       the postcondition uniquely determines the result
-/

section Specs

-- Helper Functions

-- Check if an element is a majority element (appears more than n/2 times)
def isMajorityElement (nums : List Int) (x : Int) : Prop :=
  nums.count x > nums.length / 2

-- Check if a majority element exists in the list
def hasMajorityElement (nums : List Int) : Prop :=
  ∃ x ∈ nums, isMajorityElement nums x

-- Postcondition clauses

-- The result must be in the list
def ensures1 (nums : List Int) (result : Int) :=
  result ∈ nums

-- The result must appear more than n/2 times (majority element definition)
def ensures2 (nums : List Int) (result : Int) :=
  nums.count result > nums.length / 2

def precondition (nums : List Int) :=
  nums.length > 0 ∧ hasMajorityElement nums

def postcondition (nums : List Int) (result : Int) :=
  ensures1 nums result ∧ ensures2 nums result

end Specs

section Impl

method majorityElement (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: Simple list with majority element 3
def test1_nums : List Int := [3, 2, 3]
def test1_Expected : Int := 3

-- Test case 2: Longer list with majority element 2
def test2_nums : List Int := [2, 2, 1, 1, 1, 2, 2]
def test2_Expected : Int := 2

-- Test case 3: Single element list
def test3_nums : List Int := [1]
def test3_Expected : Int := 1

-- Test case 4: Majority element with multiple other elements
def test4_nums : List Int := [4, 4, 4, 4, 4, 2, 2, 3, 3]
def test4_Expected : Int := 4

-- Test case 5: Majority element scattered throughout
def test5_nums : List Int := [9, 8, 9, 9, 7, 9, 6, 9, 9]
def test5_Expected : Int := 9

-- Test case 6: Majority element 0 with positive element
def test6_nums : List Int := [0, 0, 0, 0, 1]
def test6_Expected : Int := 0

-- Test case 7: Large positive and negative values
def test7_nums : List Int := [100000, 100000, 100000, 100000, -100000]
def test7_Expected : Int := 100000

-- Test case 8: Negative majority element
def test8_nums : List Int := [-1, -1, -1, -1, 0, 1, 2]
def test8_Expected : Int := -1

-- Test case 9: All same elements
def test9_nums : List Int := [5, 5, 5, 5, 5, 5, 5]
def test9_Expected : Int := 5

-- Test case 10: Majority at the end
def test10_nums : List Int := [1, 2, 3, 3, 3, 3, 3]
def test10_Expected : Int := 3

-- Recommend to validate: 1, 2, 3

end TestCases
