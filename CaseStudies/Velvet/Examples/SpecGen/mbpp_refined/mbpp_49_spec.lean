import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    ExtractNthElements: Extract the element at position n from each sublist
    Natural language breakdown:
    1. Given a list of lists and an index n
    2. For each sublist that has length > n, extract the element at position n
    3. Skip sublists with length ≤ n
    4. Preserve the order of sublists
    5. Example: extractNthElements([[1,2,3], [4,5], [6,7,8,9]], 1) → [2, 5, 7]
-/

-- Helper Functions

-- Extract element at index n if the list is long enough

section Specs

-- Helper Functions

def extractAt (lst : List Nat) (n : Nat) : Option Nat :=
  if n < lst.length then lst[n]? else none

-- Filter and map: extract nth element from each sublist that's long enough
def filterMapExtract (lists : List (List Nat)) (n : Nat) : List Nat :=
  lists.filterMap (fun sublist => extractAt sublist n)

-- Postcondition clauses
def ensures1 (lists : List (List Nat)) (n : Nat) (result : List Nat) :=
  result = filterMapExtract lists n

def precondition (lists : List (List Nat)) (n : Nat) :=
  True  -- no preconditions
def postcondition (lists : List (List Nat)) (n : Nat) (result : List Nat) :=
  ensures1 lists n result

end Specs

section Impl

method ExtractNthElements (lists : List (List Nat)) (n : Nat)
  return (result : List Nat)
  require precondition lists n
  ensures postcondition lists n result
  do
    sorry

prove_correct ExtractNthElements by sorry

end Impl

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
def test1_lists : List (List Nat) := [[1, 2, 3], [4, 5], [6, 7, 8, 9]]
def test1_n : Nat := 1
def test1_Expected : List Nat := [2, 5, 7]

-- Test case 2: Extract first elements (index 0)
def test2_lists : List (List Nat) := [[1, 2, 3], [4, 5], [6, 7, 8, 9]]
def test2_n : Nat := 0
def test2_Expected : List Nat := [1, 4, 6]

-- Test case 3: Some sublists too short
def test3_lists : List (List Nat) := [[1, 2], [3], [4, 5, 6]]
def test3_n : Nat := 2
def test3_Expected : List Nat := [6]

-- Test case 4: All sublists too short
def test4_lists : List (List Nat) := [[1], [2], [3]]
def test4_n : Nat := 1
def test4_Expected : List Nat := []

-- Test case 5: Empty input
def test5_lists : List (List Nat) := []
def test5_n : Nat := 0
def test5_Expected : List Nat := []

-- Test case 6: Input with empty sublists
def test6_lists : List (List Nat) := [[], [1, 2, 3], [], [4, 5]]
def test6_n : Nat := 1
def test6_Expected : List Nat := [2, 5]

-- Test case 7: Large index
def test7_lists : List (List Nat) := [[1, 2, 3], [4, 5, 6, 7, 8]]
def test7_n : Nat := 4
def test7_Expected : List Nat := [8]

-- Test case 8: Single sublist with multiple elements
def test8_lists : List (List Nat) := [[10, 20, 30, 40, 50]]
def test8_n : Nat := 2
def test8_Expected : List Nat := [30]

-- Test case 9: All sublists have exactly n+1 elements
def test9_lists : List (List Nat) := [[1, 2], [3, 4], [5, 6]]
def test9_n : Nat := 1
def test9_Expected : List Nat := [2, 4, 6]

-- Test case 10: Mix of different types (using Int)
def test10_lists : List (List Int) := [[-1, -2, -3], [0], [1, 2]]
def test10_n : Nat := 1
def test10_Expected : List Int := [-2, 2]

-- Test case 11: Large 2D list
def test11_lists : List (List Nat) := [[1,2,3,4,5], [6,7,8], [9,10,11,12], [13], [14,15,16,17,18,19]]
def test11_n : Nat := 3
def test11_Expected : List Nat := [4, 12, 17]

-- Test case 12: Duplicate values at index n
def test12_lists : List (List Nat) := [[1, 5], [2, 5], [3, 5]]
def test12_n : Nat := 1
def test12_Expected : List Nat := [5, 5, 5]

-- Recommend to validate: test cases 1, 3, 4, 5, 6, 9
-- These cover:
-- - Test 1: Problem statement example (required)
-- - Test 3: Partial filtering
-- - Test 4: All filtered out
-- - Test 5: Empty input
-- - Test 6: Empty sublists
-- - Test 9: All qualify

end TestCases
