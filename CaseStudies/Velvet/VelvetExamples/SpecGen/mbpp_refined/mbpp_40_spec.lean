import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    ElementFrequency: Find frequency of elements in a list of lists, returning counts in descending order
    Natural language breakdown:
    1. Given a list of lists, flatten them and count frequency of each element
    2. Return element-count pairs sorted by count (descending)
    3. For ties (same count), break by first occurrence in the flattened list
    4. Empty input returns empty result
-/

-- Helper Functions

-- Flatten a list of lists into a single list

specdef FindFrequencySpec

-- Helper Functions

def countElem (list : List Nat) (elem : Nat) : Nat :=
  list.count elem

def firstIndex (list : List Nat) (elem : Nat) : Nat :=
  match list.findIdx? (· = elem) with
  | some idx => idx
  | none => list.length

def isSortedByCountAndOccurrence (flatList : List Nat) (result : List (Nat × Nat)) : Prop :=
  ∀ i j, i < j → j < result.length →
    let vi := result[i]!.1
    let vj := result[j]!.1
    let fi := result[i]!.2
    let fj := result[j]!.2
    let idxi := firstIndex flatList vi
    let idxj := firstIndex flatList vj
    (fi > fj) ∨ (fi = fj ∧ idxi < idxj)

-- Postcondition clauses
def ensures1 (lists : List (List Nat)) (result : List (Nat × Nat)) :=
  (∀ p ∈ result, p.2 = countElem lists.flatten p.1)

def ensures2 (lists : List (List Nat)) (result : List (Nat × Nat)) :=
  (∀ elem ∈ lists.flatten, ∃! p ∈ result, p.1 = elem) ∧
  (∀ p ∈ result, p.1 ∈ lists.flatten)

def ensures3 (lists : List (List Nat)) (result : List (Nat × Nat)) :=
  isSortedByCountAndOccurrence lists.flatten result

def_pre (lists : List (List Nat)) :=
  True  -- no preconditions
def_post (lists : List (List Nat)) (result : List (Nat × Nat)) :=
  ensures1 lists result ∧
  ensures2 lists result ∧
  ensures3 lists result

specend FindFrequencySpec

method FindFrequency (lists : List (List Nat))
  return (result : List (Nat × Nat))
  require FindFrequencySpec.pre lists
  ensures FindFrequencySpec.post lists result
  do
    sorry

prove_correct FindFrequency by sorry

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
def test1_lists : List (List Nat) := [[1, 2, 3, 2], [4, 5, 6, 2], [7, 1, 9, 5]]
def test1_Expected : List (Nat × Nat) := [(2, 3), (1, 2), (5, 2), (3, 1), (4, 1), (6, 1), (7, 1), (9, 1)]
-- Flattened: [1, 2, 3, 2, 4, 5, 6, 2, 7, 1, 9, 5]
-- 2 appears 3 times (index 1), 1 appears 2 times (index 0), 5 appears 2 times (index 5)
-- Tie: 1 vs 5 both have count 2, but 1 appears first (index 0 < 5)

-- Test case 2: Empty list of lists
def test2_lists : List (List Nat) := []
def test2_Expected : List (Nat × Nat) := []

-- Test case 3: Single element
def test3_lists : List (List Nat) := [[42]]
def test3_Expected : List (Nat × Nat) := [(42, 1)]

-- Test case 4: All same elements
def test4_lists : List (List Nat) := [[7, 7], [7, 7, 7]]
def test4_Expected : List (Nat × Nat) := [(7, 5)]

-- Test case 5: Multiple occurrences across sublists
def test5_lists : List (List Nat) := [[1, 2], [2, 3], [3, 1]]
def test5_Expected : List (Nat × Nat) := [(1, 2), (2, 2), (3, 2)]
-- All have count 2, ordered by first occurrence: 1 (index 0), 2 (index 1), 3 (index 2)

-- Test case 6: Empty sublists
def test6_lists : List (List Nat) := [[], [1, 2], [], [3]]
def test6_Expected : List (Nat × Nat) := [(1, 1), (2, 1), (3, 1)]

-- Test case 7: All empty sublists
def test7_lists : List (List Nat) := [[], [], []]
def test7_Expected : List (Nat × Nat) := []

-- Test case 8: Large frequency count
def test8_lists : List (List Nat) := [[1, 1, 1], [1, 1], [1, 1, 1, 1]]
def test8_Expected : List (Nat × Nat) := [(1, 9)]

-- Test case 9: Mixed frequencies
def test9_lists : List (List Nat) := [[10, 20, 30], [10, 20], [10]]
def test9_Expected : List (Nat × Nat) := [(10, 3), (20, 2), (30, 1)]

-- Test case 10: Many unique elements with same frequency
def test10_lists : List (List Nat) := [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
def test10_Expected : List (Nat × Nat) := [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (8, 1), (9, 1)]
-- All have count 1, ordered by first occurrence

-- Test case 11: Complex tie-breaking scenario
def test11_lists : List (List Nat) := [[3, 1, 2], [1, 3], [2], [4, 5]]
def test11_Expected : List (Nat × Nat) := [(3, 2), (1, 2), (2, 2), (4, 1), (5, 1)]
-- Flattened: [3, 1, 2, 1, 3, 2, 4, 5]
-- Count 2: 3 (index 0), 1 (index 1), 2 (index 2) - ordered by first index
-- Count 1: 4 (index 6), 5 (index 7) - ordered by first index

-- Test case 12: Large scale with duplicates
def test12_lists : List (List Nat) := [
  [1, 2, 3, 4, 5],
  [1, 2, 3, 4, 5],
  [1, 2, 3],
  [6, 7, 8, 9, 10]
]
def test12_Expected : List (Nat × Nat) := [
  (1, 3), (2, 3), (3, 3), (4, 2), (5, 2),
  (6, 1), (7, 1), (8, 1), (9, 1), (10, 1)
]
-- Count 3: 1, 2, 3 ordered by first occurrence
-- Count 2: 4, 5 ordered by first occurrence
-- Count 1: 6, 7, 8, 9, 10 ordered by first occurrence

-- Recommend to validate: test cases 1, 2, 3, 5, 9, 11
-- These cover:
-- - Test 1: Problem statement example with tie-breaking
-- - Test 2: Empty input
-- - Test 3: Single element
-- - Test 5: All same frequency tie-breaking
-- - Test 9: Descending frequency order
-- - Test 11: Complex tie-breaking at different levels

end TestCases
