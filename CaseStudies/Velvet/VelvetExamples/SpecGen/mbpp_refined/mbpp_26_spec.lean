import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    CheckAllKElements: Check if all elements in all tuples equal the value k
    Natural language breakdown:
    1. We have a list of lists (representing tuples)
    2. We are given a value k of the same type as the elements
    3. We need to check if EVERY ELEMENT in EVERY LIST equals k (not the length!)
    4. The function should return true if all elements in all lists equal k, false otherwise
    5. Edge case: Empty outer list should return true (vacuously true - no elements to check)
    6. Edge case: Lists containing empty sublists should return true for those sublists (no elements to violate)
    7. Example that clarifies this:
       - Input: [[4, 4], [4, 4, 4], [4, 4], [4, 4, 4, 4], [4]], k=4
       - Note: tuple lengths are [2, 3, 2, 4, 1] - NOT all equal to 4!
       - But EVERY element value is 4
       - Output: True
    8. Counter-example:
       - Input: [[4, 4], [4, 5], [4, 4]], k=4
       - The element 5 in the second list does not equal 4
       - Output: False
-/

-- Helper Functions

-- Check if all elements in a single list equal k

section Specs

-- Helper Functions

def allElementsEqualK (lst : List Nat) (k : Nat) : Prop :=
  ∀ elem ∈ lst, elem = k

-- Check if all elements in all lists equal k
def allListsHaveAllElementsK (lists : List (List Nat)) (k : Nat) : Prop :=
  ∀ lst ∈ lists, allElementsEqualK lst k

-- Postcondition clauses
def ensures1 (lists : List (List Nat)) (k : Nat) (result : Bool) :=
  result = true ↔ allListsHaveAllElementsK lists k

def precondition (lists : List (List Nat)) (k : Nat) :=
  True  -- no preconditions
def postcondition (lists : List (List Nat)) (k : Nat) (result : Bool) :=
  ensures1 lists k result

end Specs

method CheckAllKElements (lists : List (List Nat)) (k : Nat)
  return (result : Bool)
  require precondition lists k
  ensures postcondition lists k result
  do
    sorry

prove_correct CheckAllKElements by sorry

section TestCases

-- Test case 1: Example from problem statement (REQUIRED)
-- lists = [[4, 4], [4, 4, 4], [4, 4], [4, 4, 4, 4], [4]], k = 4
-- Tuple lengths: [2, 3, 2, 4, 1] - NOT all equal to 4!
-- But ALL element values are 4
-- Expected result: true
def test1_lists : List (List Nat) := [[4, 4], [4, 4, 4], [4, 4], [4, 4, 4, 4], [4]]
def test1_k : Nat := 4
def test1_Expected : Bool := true

-- Test case 2: All elements equal k, uniform list sizes
-- lists = [[3, 3], [3, 3], [3, 3]], k = 3
-- All elements are 3
-- Expected result: true
def test2_lists : List (List Nat) := [[3, 3], [3, 3], [3, 3]]
def test2_k : Nat := 3
def test2_Expected : Bool := true

-- Test case 3: One element differs
-- lists = [[4, 4], [4, 5], [4, 4]], k = 4
-- The element 5 in second list does not equal 4
-- Expected result: false
def test3_lists : List (List Nat) := [[4, 4], [4, 5], [4, 4]]
def test3_k : Nat := 4
def test3_Expected : Bool := false

-- Test case 4: Empty outer list (vacuously true)
-- lists = [], k = 5
-- No elements to check
-- Expected result: true
def test4_lists : List (List Nat) := []
def test4_k : Nat := 5
def test4_Expected : Bool := true

-- Test case 5: Lists with empty sublists
-- lists = [[2, 2], [], [2], []], k = 2
-- Empty lists have no elements, non-empty lists have all 2s
-- Expected result: true
def test5_lists : List (List Nat) := [[2, 2], [], [2], []]
def test5_k : Nat := 2
def test5_Expected : Bool := true

-- Test case 6: Single element lists, all equal k
-- lists = [[7], [7], [7], [7]], k = 7
-- All elements equal 7
-- Expected result: true
def test6_lists : List (List Nat) := [[7], [7], [7], [7]]
def test6_k : Nat := 7
def test6_Expected : Bool := true

-- Test case 7: Single element differs in single-element list
-- lists = [[7], [7], [8], [7]], k = 7
-- Third list contains 8, not 7
-- Expected result: false
def test7_lists : List (List Nat) := [[7], [7], [8], [7]]
def test7_k : Nat := 7
def test7_Expected : Bool := false

-- Test case 8: Large lists with varying sizes, all elements equal k
-- lists = [[1], [1, 1, 1], [1, 1], [1, 1, 1, 1, 1]], k = 1
-- All elements are 1, despite different list sizes
-- Expected result: true
def test8_lists : List (List Nat) := [[1], [1, 1, 1], [1, 1], [1, 1, 1, 1, 1]]
def test8_k : Nat := 1
def test8_Expected : Bool := true

-- Test case 9: All zeros
-- lists = [[0, 0, 0], [0], [0, 0]], k = 0
-- All elements are 0
-- Expected result: true
def test9_lists : List (List Nat) := [[0, 0, 0], [0], [0, 0]]
def test9_k : Nat := 0
def test9_Expected : Bool := true

-- Test case 10: Mix of correct and incorrect elements
-- lists = [[5, 5, 5], [5, 5, 5], [5, 5, 6]], k = 5
-- Last element in last list is 6, not 5
-- Expected result: false
def test10_lists : List (List Nat) := [[5, 5, 5], [5, 5, 5], [5, 5, 6]]
def test10_k : Nat := 5
def test10_Expected : Bool := false

-- Test case 11: First element differs
-- lists = [[9, 10, 10], [10, 10]], k = 10
-- First element of first list is 9, not 10
-- Expected result: false
def test11_lists : List (List Nat) := [[9, 10, 10], [10, 10]]
def test11_k : Nat := 10
def test11_Expected : Bool := false

-- Test case 12: Large scale test with many lists
-- lists = [[2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]], k = 2
-- Many lists, all elements are 2
-- Expected result: true
def test12_lists : List (List Nat) := [[2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]
def test12_k : Nat := 2
def test12_Expected : Bool := true

-- Test case 13: All empty lists
-- lists = [[], [], []], k = 100
-- All lists are empty, no elements to check
-- Expected result: true
def test13_lists : List (List Nat) := [[], [], []]
def test13_k : Nat := 100
def test13_Expected : Bool := true

-- Test case 14: Single non-empty list, all elements equal k
-- lists = [[8, 8, 8, 8, 8, 8]], k = 8
-- Single list with all 8s
-- Expected result: true
def test14_lists : List (List Nat) := [[8, 8, 8, 8, 8, 8]]
def test14_k : Nat := 8
def test14_Expected : Bool := true

-- Test case 15: Diverse list sizes with one mismatch
-- lists = [[3], [3, 3, 3, 3, 3], [3, 3], [3, 3, 3]], k = 3
-- All look good, but let's make one fail
def test15_lists : List (List Nat) := [[3], [3, 3, 4, 3, 3], [3, 3], [3, 3, 3]]
def test15_k : Nat := 3
def test15_Expected : Bool := false

-- Recommend to validate: test cases 1, 2, 3, 5, 8, 13
-- These cover:
-- - Test 1: Problem statement example (required) - varying sizes, all elements equal k
-- - Test 2: Uniform sizes, all elements equal k (typical case)
-- - Test 3: One element differs (typical failure)
-- - Test 5: Empty sublists mixed with non-empty (edge case)
-- - Test 8: Large varying sizes, all elements equal k (stress test)
-- - Test 13: All empty lists (edge case)

end TestCases
