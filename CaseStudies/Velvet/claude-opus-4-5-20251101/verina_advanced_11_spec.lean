import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findMajorityElement: Find the majority element in a list of integers
    Natural language breakdown:
    1. We are given a list of integers (may include duplicates and negative numbers)
    2. A majority element is defined as an element that appears strictly more than half the number of times in the list
    3. Formally, element x is a majority element if lst.count x > lst.length / 2
    4. If such a majority element exists, return that element
    5. If no majority element exists, return -1
    6. Edge case: Empty list has no majority element, return -1
    7. Note: There can be at most one majority element in any list (since it must appear more than half the time)
    8. The result is either the unique majority element or -1
-/

section Specs

-- Helper function to check if an element is a majority element
def isMajorityElement (lst : List Int) (x : Int) : Prop :=
  lst.count x > lst.length / 2

-- Helper function to check if a majority element exists
def hasMajorityElement (lst : List Int) : Prop :=
  ∃ x, x ∈ lst ∧ isMajorityElement lst x

-- Precondition: no restrictions on input
def precondition (lst : List Int) : Prop :=
  True

-- Postcondition: result is either the majority element or -1
def postcondition (lst : List Int) (result : Int) : Prop :=
  (hasMajorityElement lst → (result ∈ lst ∧ isMajorityElement lst result)) ∧
  (¬hasMajorityElement lst → result = -1)

end Specs

section Impl

method findMajorityElement (lst : List Int)
  return (result : Int)
  require precondition lst
  ensures postcondition lst result
  do
  pure (-1 : Int)

end Impl

section TestCases

-- Test case 1: Basic case with majority element 1
def test1_lst : List Int := [1, 2, 1, 1]
def test1_Expected : Int := 1

-- Test case 2: No majority element (all distinct)
def test2_lst : List Int := [1, 2, 3, 4]
def test2_Expected : Int := -1

-- Test case 3: Clear majority element
def test3_lst : List Int := [2, 2, 2, 2, 3, 3]
def test3_Expected : Int := 2

-- Test case 4: Empty list
def test4_lst : List Int := []
def test4_Expected : Int := -1

-- Test case 5: All same elements
def test5_lst : List Int := [5, 5, 5, 5, 5, 5]
def test5_Expected : Int := 5

-- Test case 6: Negative number appears most but not majority
def test6_lst : List Int := [-1, -1, -1, 2, 2]
def test6_Expected : Int := -1

-- Test case 7: Negative number is majority element
def test7_lst : List Int := [-3, -3, -3, -3, 1]
def test7_Expected : Int := -3

-- Test case 8: Single element list
def test8_lst : List Int := [42]
def test8_Expected : Int := 42

-- Test case 9: Two elements same
def test9_lst : List Int := [7, 7]
def test9_Expected : Int := 7

-- Test case 10: Exactly half (not majority)
def test10_lst : List Int := [1, 1, 2, 2]
def test10_Expected : Int := -1

-- Recommend to validate: 1, 3, 7

end TestCases
