import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    FirstDuplicate: Find the first duplicate element in a given array of integers
    Natural language breakdown:
    1. We are given a list of integers
    2. We need to find the first element that appears more than once
    3. "First" means the duplicate pair with the smallest second occurrence index
    4. If we have arr[i] = arr[j] where i < j, then (i,j) is a duplicate pair
    5. Among all such duplicate pairs, we want the one where j is minimal
    6. The result is the value at indices i and j in that minimal pair
    7. If no duplicates exist, return None
    8. The specification should be simple and direct:
       - When result is Some(x): there exist indices i < j with arr[i] = arr[j] = x,
         and for any other pair i' < j' with arr[i'] = arr[j'], we have j ≤ j'
       - When result is None: no such duplicate pair exists
    9. Edge cases:
       - Empty list: no duplicates, return None
       - Single element: no duplicates, return None
       - All distinct elements: return None
       - Multiple duplicates: return the one with earliest second occurrence
-/

-- Helper Functions
-- None needed for this simplified specification

section Specs

-- Postcondition clauses
def ensures1 (arr : List Int) (result : Option Int) :=
  match result with
  | none => ∀ i j, i < j → j < arr.length → arr[i]! ≠ arr[j]!
  | some x =>
      ∃ i j, (i < j ∧ j < arr.length ∧ arr[i]! = x ∧ arr[j]! = x) ∧
              (∀ i' j', i' < j' → j' < arr.length → arr[i']! = arr[j']! → j ≤ j')

def precondition (arr : List Int) :=
  True  -- no preconditions
def postcondition (arr : List Int) (result : Option Int) :=
  ensures1 arr result

end Specs

section Impl

method FirstDuplicate (arr: List Int)
  return (result: Option Int)
  require precondition arr
  ensures postcondition arr result
  do
    sorry

prove_correct FirstDuplicate by sorry

end Impl

section TestCases

-- Test case 1: Basic duplicate in middle of array (from problem statement)
def test0_arr : List Int := [1, 2, 3, 4, 4, 5]
def test0_Expected : Option Int := some 4

-- Test case 2: Multiple duplicates, return earliest second occurrence
def test1_arr : List Int := [1, 2, 3, 2, 4, 1]
def test1_Expected : Option Int := some 2

-- Test case 3: No duplicates
def test2_arr : List Int := [1, 2, 3, 4, 5]
def test2_Expected : Option Int := none

-- Test case 4: Duplicate at beginning
def test3_arr : List Int := [1, 1, 2, 3]
def test3_Expected : Option Int := some 1

-- Test case 5: Empty list
def test4_arr : List Int := []
def test4_Expected : Option Int := none

-- Test case 6: All same elements
def test6_arr : List Int := [7, 7, 7, 7]
def test6_Expected : Option Int := some 7

-- Test case 7: Negative numbers
def test7_arr : List Int := [-1, -2, -1, 0]
def test7_Expected : Option Int := some (-1)

-- Test case 8: Zero duplicate
def test8_arr : List Int := [0, 1, 2, 0]
def test8_Expected : Option Int := some 0

-- Test case 9: Large array with duplicate at end
def test10_arr : List Int := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 1]
def test10_Expected : Option Int := some 1

-- Recommend to validate: test cases 0, 1, 2, 3, 4, 6
-- These cover:
-- - Test 0: Example from problem statement (required)
-- - Test 1: Multiple duplicates (tests "first" semantics - earliest second occurrence)
-- - Test 2: No duplicates edge case
-- - Test 3: Duplicate at start
-- - Test 4: Empty list edge case
-- - Test 6: All identical elements

end TestCases
