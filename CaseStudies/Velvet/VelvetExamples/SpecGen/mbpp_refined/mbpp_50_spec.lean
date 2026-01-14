import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    MBPP Problem 50: Find the list with minimum length using lambda function

    Natural language breakdown:
    1. We are given a collection of lists (a list of lists)
    2. We need to find and return a tuple containing: (minimum_length, list_with_minimum_length)
    3. The minimum length is the smallest length among all lists in the collection
    4. The returned list is the list from the collection that has the minimum length
    5. If multiple lists have the same minimum length, we return the first one encountered
    6. The input should be non-empty (we need at least one list to find the minimum)
    7. The returned list must be one of the lists from the input collection
    8. The length of the returned list must be equal to the minimum length
    9. The minimum length must be less than or equal to the length of any other list in the collection
    10. Edge case: If there's only one list, return that list with its length
    11. Edge case: If some lists are empty, an empty list should be returned with length 0
-/



-- Helper Functions

-- Find the index of the first list with the given length

section Specs

-- Helper Functions

def findFirstIndex (lists : List (List Nat)) (len : Nat) : Option Nat :=
  lists.findIdx? (fun l => l.length = len)

-- Check if a list is the first occurrence of a list with the given length
def isFirstWithLength (lists : List (List Nat)) (target : List Nat) (len : Nat) : Prop :=
  target ∈ lists ∧ target.length = len ∧
  (∀ i < lists.length, lists[i]!.length = len →
    ∃ j ≤ i, j < lists.length ∧ lists[j]! = target)

def require1 (lists : List (List Nat)) :=
  lists.length > 0

-- Postcondition clauses
def ensures1 (lists : List (List Nat)) (result : (Nat × List Nat)) :=
  result.2 ∈ lists
def ensures2 (lists : List (List Nat)) (result : (Nat × List Nat)) :=
  result.2.length = result.1
def ensures3 (lists : List (List Nat)) (result : (Nat × List Nat)) :=
  ∀ other ∈ lists, result.1 ≤ other.length
def ensures4 (lists : List (List Nat)) (result : (Nat × List Nat)) :=
  isFirstWithLength lists result.2 result.1

def precondition (lists : List (List Nat)) :=
  require1 lists
def postcondition (lists : List (List Nat)) (result : (Nat × List Nat)) :=
  ensures1 lists result ∧
  ensures2 lists result ∧
  ensures3 lists result ∧
  ensures4 lists result

end Specs

section Impl

method MinLengthList (lists : List (List Nat))
  return (result : (Nat × List Nat))
  require precondition lists
  ensures postcondition lists result
  do
    sorry

prove_correct MinLengthList by sorry

end Impl

section TestCases

-- Test case 1: Original MBPP test case 1 (REQUIRED - from problem statement)
-- Lists: [[0], [1, 3], [5, 7], [9, 11], [13, 15, 17]]
-- Expected: (1, [0])
def test1_lists : List (List Nat) := [[0], [1, 3], [5, 7], [9, 11], [13, 15, 17]]
def test1_Expected : (Nat × List Nat) := (1, [0])

-- Test case 2: Original MBPP test case 2
-- Lists: [[1,2,3,4,5],[1,2,3,4],[1,2,3],[1,2],[1]]
-- Expected: (1, [1])
def test2_lists : List (List Nat) := [[1,2,3,4,5], [1,2,3,4], [1,2,3], [1,2], [1]]
def test2_Expected : (Nat × List Nat) := (1, [1])

-- Test case 3: Original MBPP test case 3
-- Lists: [[3,4,5],[6,7,8,9],[10,11,12],[1,2]]
-- Expected: (2, [1,2])
def test3_lists : List (List Nat) := [[3,4,5], [6,7,8,9], [10,11,12], [1,2]]
def test3_Expected : (Nat × List Nat) := (2, [1,2])

-- Test case 4: Contains an empty list (minimum possible length)
-- Lists: [[1,2,3], [], [4,5]]
-- Expected: (0, [])
def test4_lists : List (List Nat) := [[1,2,3], [], [4,5]]
def test4_Expected : (Nat × List Nat) := (0, [])

-- Test case 5: Single list (edge case)
-- Lists: [[1,2,3,4,5]]
-- Expected: (5, [1,2,3,4,5])
def test5_lists : List (List Nat) := [[1,2,3,4,5]]
def test5_Expected : (Nat × List Nat) := (5, [1,2,3,4,5])

-- Test case 6: Multiple empty lists - should return first empty list
-- Lists: [[], [], [1,2]]
-- Expected: (0, [])
def test6_lists : List (List Nat) := [[], [], [1,2]]
def test6_Expected : (Nat × List Nat) := (0, [])

-- Test case 7: All lists have the same length - should return first
-- Lists: [[1,2], [3,4], [5,6]]
-- Expected: (2, [1,2])
def test7_lists : List (List Nat) := [[1,2], [3,4], [5,6]]
def test7_Expected : (Nat × List Nat) := (2, [1,2])

-- Test case 8: Duplicate lists with minimum length
-- Lists: [[1,2,3], [4], [5], [6,7]]
-- Expected: (1, [4]) - first list with minimum length
def test8_lists : List (List Nat) := [[1,2,3], [4], [5], [6,7]]
def test8_Expected : (Nat × List Nat) := (1, [4])

-- Test case 9: Large variation in lengths
-- Lists: [[1], [1,2,3,4,5,6,7,8,9,10], [1,2], [1,2,3,4,5]]
-- Expected: (1, [1])
def test9_lists : List (List Nat) := [[1], [1,2,3,4,5,6,7,8,9,10], [1,2], [1,2,3,4,5]]
def test9_Expected : (Nat × List Nat) := (1, [1])

-- Test case 10: Large scale test with many lists
-- Lists: 20 lists with varying lengths from 1 to 20
-- Expected: (0, []) - List.range 1 produces [0] which has length 1, but List.range 0 produces [] with length 0
def test10_lists : List (List Nat) :=
  [List.range 20, List.range 19, List.range 18, List.range 17, List.range 16,
   List.range 15, List.range 14, List.range 13, List.range 12, List.range 11,
   List.range 10, List.range 9, List.range 8, List.range 7, List.range 6,
   List.range 5, List.range 4, List.range 3, List.range 2, List.range 1, List.range 0]
def test10_Expected : (Nat × List Nat) := (0, [])

-- Test case 11: Lists with negative numbers
-- Lists: [[-5,-4,-3], [-2], [-1,0,1,2,3]]
-- Expected: (1, [-2])
def test11_lists : List (List Int) := [[-5,-4,-3], [-2], [-1,0,1,2,3]]
def test11_Expected : (Int × List Int) := (1, [-2])

-- Test case 12: Lists with characters (testing polymorphism)
-- Lists: [['a','b','c'], ['d'], ['e','f']]
-- Expected: (1, ['d'])
def test12_lists : List (List Char) := [['a','b','c'], ['d'], ['e','f']]
def test12_Expected : (Nat × List Char) := (1, ['d'])

-- Test case 13: Very long lists with one short list
-- Lists: [[1..100], [1..50], [1], [1..75]]
-- Expected: (1, [1])
def test13_lists : List (List Nat) := [List.range 100, List.range 50, [1], List.range 75]
def test13_Expected : (Nat × List Nat) := (1, [1])

-- Test case 14: All empty lists - should return first
-- Lists: [[], [], []]
-- Expected: (0, [])
def test14_lists : List (List Nat) := [[], [], []]
def test14_Expected : (Nat × List Nat) := (0, [])

-- Test case 15: Two minimum length lists - ensure first is returned
-- Lists: [[10,20], [30], [40], [50,60,70]]
-- Expected: (1, [30]) - first list with length 1
def test15_lists : List (List Nat) := [[10,20], [30], [40], [50,60,70]]
def test15_Expected : (Nat × List Nat) := (1, [30])

-- Recommend to validate: test cases 1, 2, 3, 4, 5, 8
-- These cover:
-- - Tests 1-3: Original MBPP test cases (required)
-- - Test 4: Empty list edge case
-- - Test 5: Single list edge case
-- - Test 8: Duplicate minimum lengths (tests first occurrence)

end TestCases
