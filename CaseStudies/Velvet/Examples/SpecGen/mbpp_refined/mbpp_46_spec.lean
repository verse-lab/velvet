import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    AllDifferent: Determine whether all the numbers in a list are different from each other
    Natural language breakdown:
    1. We have an input list of integers
    2. "All different" means that no two elements in the list have the same value
    3. The function should return true if all elements are unique (pairwise distinct)
    4. The function should return false if there exists at least one duplicate
    5. An empty list has all different elements (vacuously true - returns true)
    6. A single-element list has all different elements (returns true)
    7. The order of elements doesn't matter - we only check for distinctness
    8. The position of elements doesn't affect the result

    Property-oriented specification:
    - If result is true: for any two different positions i and j in the list,
      the elements at those positions are different
    - If result is false: there exist two different positions i and j in the list
      such that the elements at those positions are equal
    - This is the logical negation of the "has duplicates" predicate
-/

-- Helper Functions

-- Predicate: check if all elements in a list are pairwise distinct
-- All elements are different if no two distinct indices have the same value

section Specs

-- Helper Functions

def allDifferent (lst: List Int) : Prop :=
  ∀ i j, i < lst.length → j < lst.length → i ≠ j → lst[i]! ≠ lst[j]!

-- Postcondition clauses
def ensures1 (lst : List Int) (result : Bool) :=
  result = true ↔ allDifferent lst

def precondition (lst : List Int) :=
  True  -- no preconditions
def postcondition (lst : List Int) (result : Bool) :=
  ensures1 lst result

end Specs

section Impl

method AllNumbersDifferent (lst: List Int)
  return (result: Bool)
  require precondition lst
  ensures postcondition lst result
  do
    sorry

prove_correct AllNumbersDifferent by sorry

end Impl

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
def test1_lst : List Int := [1, 5, 7, 9]
def test1_Expected : Bool := true

-- Test case 2: Has duplicate - 2 appears twice
def test2_lst : List Int := [1, 2, 3, 2, 4]
def test2_Expected : Bool := false

-- Test case 3: Empty list (vacuously all different)
def test3_lst : List Int := []
def test3_Expected : Bool := true

-- Test case 4: Single element (all different)
def test4_lst : List Int := [42]
def test4_Expected : Bool := true

-- Test case 5: Two different elements
def test5_lst : List Int := [1, 2]
def test5_Expected : Bool := true

-- Test case 6: Two identical elements
def test6_lst : List Int := [5, 5]
def test6_Expected : Bool := false

-- Test case 7: All same elements
def test7_lst : List Int := [3, 3, 3, 3]
def test7_Expected : Bool := false

-- Test case 8: Negative numbers all different
def test8_lst : List Int := [-5, -3, -1, 0, 2, 4]
def test8_Expected : Bool := true

-- Test case 9: Negative numbers with duplicate
def test9_lst : List Int := [-1, -2, -3, -1]
def test9_Expected : Bool := false

-- Test case 10: Zero with duplicates
def test10_lst : List Int := [0, 1, 2, 0]
def test10_Expected : Bool := false

-- Test case 11: Zero without duplicates
def test11_lst : List Int := [-1, 0, 1, 2]
def test11_Expected : Bool := true

-- Test case 12: Multiple duplicates
def test12_lst : List Int := [1, 2, 1, 3, 2, 4]
def test12_Expected : Bool := false

-- Test case 13: Large list all different
def test13_lst : List Int :=
  [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
   21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,
   41,42,43,44,45,46,47,48,49,50]
def test13_Expected : Bool := true

-- Test case 14: Large list with one duplicate at end
def test14_lst : List Int :=
  [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
   21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,
   41,42,43,44,45,46,47,48,49,50,1]
def test14_Expected : Bool := false

-- Test case 15: Large list with duplicate in middle
def test15_lst : List Int :=
  [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
   21,22,23,24,25,5,26,27,28,29,30]
def test15_Expected : Bool := false

-- Test case 16: Mix of positive and negative, all different
def test16_lst : List Int := [-10, -5, 0, 5, 10, 15, 20]
def test16_Expected : Bool := true

-- Test case 17: Sequential numbers (all different)
def test17_lst : List Int := [100, 101, 102, 103, 104, 105]
def test17_Expected : Bool := true

-- Test case 18: Non-sequential but all different
def test18_lst : List Int := [7, 3, 11, 2, 19, 5, 13]
def test18_Expected : Bool := true

-- Recommend to validate: test cases 1, 2, 3, 4, 6, 13
-- These cover:
-- - Test 1: Problem statement example (required) - all different
-- - Test 2: Has duplicates (returns false)
-- - Test 3: Empty list edge case
-- - Test 4: Single element edge case
-- - Test 6: Minimal duplicate case
-- - Test 13: Large scale all different

end TestCases
