import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    firstDuplicate: Find the first duplicate integer in a list when scanning left to right
    Natural language breakdown:
    1. We are given a list of integers
    2. We scan from left to right, looking for the first element that has appeared before
    3. "First duplicate" means the first position j where lst[j] equals some earlier lst[i] (i < j)
    4. We want to find the smallest index j such that lst[j] appears in lst[0..j-1]
    5. The result is the value at that index j
    6. If no such duplicate exists, return none
    7. Edge cases:
       - Empty list: no duplicates, return none
       - Single element: no duplicates, return none
       - All distinct elements: return none
       - Multiple duplicates: return the one with earliest second occurrence
    8. Key insight: We're looking for the first index j where (List.take j lst).contains lst[j]!
-/

section Specs

-- Helper: Check if element at index j appeared in the prefix lst[0..j-1]
-- Using List.take and List.contains as suggested by LeanExplore

-- Postcondition: Characterize the first duplicate
-- When result is some x:
--   - There exists an index j where lst[j]! = x and x appears in lst[0..j-1]
--   - j is the smallest such index (no earlier index has this property)
-- When result is none:
--   - No element appears twice (no index j has lst[j]! in its prefix)

def precondition (lst : List Int) :=
  True  -- no preconditions

def postcondition (lst : List Int) (result : Option Int) :=
  match result with
  | none =>
      -- No element appears in its prefix (no duplicates)
      ∀ j : Nat, j < lst.length → ¬((lst.take j).contains lst[j]!)
  | some x =>
      -- There exists a position j where:
      -- 1. lst[j]! = x
      -- 2. x appears in the prefix lst[0..j-1]
      -- 3. j is minimal (no earlier position has an element appearing in its prefix)
      ∃ j : Nat, j < lst.length ∧
                 lst[j]! = x ∧
                 (lst.take j).contains x ∧
                 (∀ k : Nat, k < j → ¬((lst.take k).contains lst[k]!))

end Specs

section Impl

method firstDuplicate (lst: List Int)
  return (result: Option Int)
  require precondition lst
  ensures postcondition lst result
  do
  pure none  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic duplicate in middle [1, 2, 3, 2, 4] -> some 2
def test1_lst : List Int := [1, 2, 3, 2, 4]
def test1_Expected : Option Int := some 2

-- Test case 2: Duplicate at end [5, 1, 2, 3, 4, 5] -> some 5
def test2_lst : List Int := [5, 1, 2, 3, 4, 5]
def test2_Expected : Option Int := some 5

-- Test case 3: No duplicates [1, 2, 3, 4, 5] -> none
def test3_lst : List Int := [1, 2, 3, 4, 5]
def test3_Expected : Option Int := none

-- Test case 4: All same elements [7, 7, 7, 7] -> some 7
def test4_lst : List Int := [7, 7, 7, 7]
def test4_Expected : Option Int := some 7

-- Test case 5: Empty list [] -> none
def test5_lst : List Int := []
def test5_Expected : Option Int := none

-- Test case 6: Negative numbers [-1, 2, -1] -> some (-1)
def test6_lst : List Int := [-1, 2, -1]
def test6_Expected : Option Int := some (-1)

-- Test case 7: Single element [42] -> none
def test7_lst : List Int := [42]
def test7_Expected : Option Int := none

-- Test case 8: Two elements, duplicate [3, 3] -> some 3
def test8_lst : List Int := [3, 3]
def test8_Expected : Option Int := some 3

-- Test case 9: Two elements, no duplicate [1, 2] -> none
def test9_lst : List Int := [1, 2]
def test9_Expected : Option Int := none

-- Test case 10: Multiple duplicates, first one wins [1, 2, 1, 2, 3] -> some 1
def test10_lst : List Int := [1, 2, 1, 2, 3]
def test10_Expected : Option Int := some 1

-- Recommend to validate: 1, 4, 6
-- Test 1: Basic case from problem description with duplicate in middle
-- Test 4: Edge case with all same elements (immediate duplicate)
-- Test 6: Tests negative numbers handling

end TestCases
