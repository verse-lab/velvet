import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    TopKFrequent: Write a function to find the top k integers that occur most frequently from given lists of sorted and distinct integers using heap queue algorithm.
    Natural language breakdown:
    1. Input: A list of lists of integers, where each inner list is sorted and contains distinct integers
    2. We need to count the frequency of each integer across all the lists (how many lists contain it)
    3. We want to find the top k integers that appear most frequently
    4. "Top k" means the k integers with the highest occurrence counts
    5. To ensure uniqueness, we define a total ordering:
       - Primary: Sort by frequency (descending) - higher frequency first
       - Tie-breaker: Sort by first occurrence index (ascending) - elements appearing earlier in the flattened input come first
    6. The result should be the first k elements from this uniquely sorted list
    7. If there are fewer than k distinct integers total, return all of them
    8. This total ordering with first-occurrence tie-breaking eliminates ambiguity when elements have equal frequency
    9. The first occurrence of an element is determined by flattening all lists in order and finding the first position where it appears
-/

-- Helper Functions

section Specs

-- Helper Functions

def countOccurrences (value: Int) (lists: List (List Int)) : Nat :=
  lists.flatten.count value

-- Find the first occurrence index of a value in the flattened list
def firstOccurrenceIndex (value: Int) (lists: List (List Int)) : Nat :=
  let flattened := lists.flatten
  match flattened.findIdx? (· = value) with
  | some idx => idx
  | none => flattened.length

-- Check if a list is sorted by: frequency (descending), then first occurrence (ascending) for ties
def isSortedByFreqThenOccurrence (sorted: List Int) (lists: List (List Int)) : Prop :=
  ∀ i j, i < j → j < sorted.length →
    let vi := sorted[i]!
    let vj := sorted[j]!
    let fi := countOccurrences vi lists
    let fj := countOccurrences vj lists
    let idxi := firstOccurrenceIndex vi lists
    let idxj := firstOccurrenceIndex vj lists
    (fi > fj) ∨ (fi = fj ∧ idxi < idxj)

def require1 (lists : List (List Int)) (k : Nat) :=
  ∀ lst ∈ lists, lst.Sorted (· ≤ ·)
def require2 (lists : List (List Int)) (k : Nat) :=
  ∀ lst ∈ lists, lst.Nodup

-- Postcondition clauses
def ensures1 (lists : List (List Int)) (k : Nat) (result : List Int) :=
  ∃ sorted : List Int,
    (∀ elem ∈ lists.flatten, ∃! p ∈ sorted, p = elem) ∧
    (∀ p ∈ result, p ∈ lists.flatten) ∧
    isSortedByFreqThenOccurrence sorted lists ∧
    result = sorted.take k

def precondition (lists : List (List Int)) (k : Nat) :=
  require1 lists k ∧require2 lists k
def postcondition (lists : List (List Int)) (k : Nat) (result : List Int) :=
  ensures1 lists k result

end Specs

section Impl

method TopKFrequent (lists: List (List Int)) (k: Nat)
  return (result: List Int)
  require precondition lists k
  ensures postcondition lists k result
  do
    sorry

prove_correct TopKFrequent by sorry

end Impl

section TestCases

-- Test case 0: Problem example (MUST be first)
-- Flattened: [1, 2, 6, 1, 3, 4, 5, 7, 8, 1, 3, 5, 6, 8, 9, 2, 5, 7, 11, 1, 4, 7, 8, 12]
-- First occurrence indices: 1→0, 2→1, 6→2, 3→4, 4→5, 5→6, 7→7, 8→8, 9→14, 11→19, 12→23
-- Frequencies: 1→4 times, 5→3 times, 7→3 times, 8→3 times, 3→2 times, 6→2 times, 2→2 times, 4→2 times, others→1 time
-- Top 3 by freq then occurrence: 1 (4), then 5,7,8 (3 each) - tie broken by first occurrence, so 5,7
def test0_lists : List (List Int) := [[1, 2, 6], [1, 3, 4, 5, 7, 8], [1, 3, 5, 6, 8, 9], [2, 5, 7, 11], [1, 4, 7, 8, 12]]
def test0_k : Nat := 3
def test0_Expected : List Int := [1, 5, 7]

-- Test case 1: Basic case with clear top frequencies
-- Flattened: [1, 2, 3, 2, 3, 4, 3, 4, 5]
-- First occurrence indices: 1→0, 2→1, 3→2, 4→5, 5→8
-- Frequencies: 3→3 times, 2→2 times, 4→2 times, 1→1 time, 5→1 time
-- Top 2: 3 (3), 2 (2, wins tie with 4 by first occurrence)
def test1_lists : List (List Int) := [[1, 2, 3], [2, 3, 4], [3, 4, 5]]
def test1_k : Nat := 2
def test1_Expected : List Int := [3, 2]

-- Test case 2: All elements appear once (tie-breaking by first occurrence)
-- Flattened: [1, 2, 3, 4]
-- All frequency 1, sorted by first occurrence: 1, 2, 3, 4
-- Top 2: 1, 2
def test2_lists : List (List Int) := [[1], [2], [3], [4]]
def test2_k : Nat := 2
def test2_Expected : List Int := [1, 2]

-- Test case 3: k larger than number of distinct elements
-- Flattened: [1, 2, 1, 2]
-- Frequencies: 1→2, 2→2
-- All elements returned, sorted by freq (2), then first occurrence: 1, 2
def test3_lists : List (List Int) := [[1, 2], [1, 2]]
def test3_k : Nat := 5
def test3_Expected : List Int := [1, 2]

-- Test case 4: Single list (all freq=1, sorted by first occurrence)
-- Flattened: [1, 2, 3, 4, 5]
-- All frequency 1, sorted by first occurrence
-- Top 3: 1, 2, 3
def test4_lists : List (List Int) := [[1, 2, 3, 4, 5]]
def test4_k : Nat := 3
def test4_Expected : List Int := [1, 2, 3]

-- Test case 5: Clear frequency ordering
-- Flattened: [1, 1, 2, 1, 2, 3, 1, 2, 3, 4]
-- First occurrence indices: 1→0, 2→2, 3→5, 4→9
-- Frequencies: 1→4 times, 2→3 times, 3→2 times, 4→1 time
def test5_lists : List (List Int) := [[1], [1, 2], [1, 2, 3], [1, 2, 3, 4]]
def test5_k : Nat := 2
def test5_Expected : List Int := [1, 2]

-- Test case 6: With negative numbers
-- Flattened: [-3, -1, 0, -1, 0, 2, 0, 2, 4]
-- First occurrence indices: -3→0, -1→1, 0→2, 2→5, 4→8
-- Frequencies: 0→3 times, -1→2 times, 2→2 times, -3→1 time, 4→1 time
-- Top 2: 0 (3), -1 (2, wins tie with 2 by first occurrence)
def test6_lists : List (List Int) := [[-3, -1, 0], [-1, 0, 2], [0, 2, 4]]
def test6_k : Nat := 2
def test6_Expected : List Int := [0, -1]

-- Test case 7: k = 1
-- Flattened: [5, 10, 15, 10, 15, 20, 10, 15, 20, 25]
-- First occurrence indices: 5→0, 10→1, 15→2, 20→5, 25→9
-- Frequencies: 10→3 times, 15→3 times, 20→2 times, others→1 time
-- Top 1: 10 (3, wins tie with 15 by first occurrence)
def test7_lists : List (List Int) := [[5, 10, 15], [10, 15, 20], [10, 15, 20, 25]]
def test7_k : Nat := 1
def test7_Expected : List Int := [10]

-- Test case 8: Large dataset scenario
-- Flattened: [1, 2, 3, 4, 5, 1, 2, 3, 1, 2, 1]
-- First occurrence indices: 1→0, 2→1, 3→2, 4→3, 5→4
-- Frequencies: 1→4 times, 2→3 times, 3→2 times, 4→1 time, 5→1 time
def test8_lists : List (List Int) := [[1, 2, 3, 4, 5], [1, 2, 3], [1, 2], [1]]
def test8_k : Nat := 3
def test8_Expected : List Int := [1, 2, 3]

-- Test case 9: Multiple ties at same frequency
-- Flattened: [1, 2, 3, 4, 1, 2, 3, 4]
-- First occurrence indices: 1→0, 2→1, 3→2, 4→3
-- All have freq=2, sorted by first occurrence: 1, 2, 3, 4
def test9_lists : List (List Int) := [[1, 2], [3, 4], [1, 2], [3, 4]]
def test9_k : Nat := 3
def test9_Expected : List Int := [1, 2, 3]

-- Test case 10: Mix of high and low frequencies with ties
-- Flattened: [1, 3, 5, 3, 5, 7, 5, 7, 9, 1, 5, 9, 2, 5]
-- First occurrence indices: 1→0, 3→1, 5→2, 7→5, 9→8, 2→12
-- Frequencies: 5→5 times, 3→2 times, 7→2 times, 1→2 times, 9→2 times, 2→1 time
-- Top 4: 5 (5), then {1,3,7,9} (2 each) - sorted by first occurrence: 1, 3, 7
def test10_lists : List (List Int) := [[1, 3, 5], [3, 5, 7], [5, 7, 9], [1, 5, 9], [2, 5]]
def test10_k : Nat := 4
def test10_Expected : List Int := [5, 1, 3, 7]

-- Test case 11: All different frequencies
-- Flattened: [1, 2, 3, 1, 2, 1]
-- First occurrence indices: 1→0, 2→1, 3→2
-- Frequencies: 1→3, 2→2, 3→1
def test11_lists : List (List Int) := [[1, 2, 3], [1, 2], [1]]
def test11_k : Nat := 2
def test11_Expected : List Int := [1, 2]

-- Test case 12: Large tie at frequency 1
-- Flattened: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
-- All frequency 1, sorted by first occurrence
def test12_lists : List (List Int) := [[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
def test12_k : Nat := 5
def test12_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 13: Reverse order appearance
-- Flattened: [5, 4, 3, 2, 1]
-- All frequency 1, sorted by first occurrence: 5, 4, 3
def test13_lists : List (List Int) := [[5], [4], [3], [2], [1]]
def test13_k : Nat := 3
def test13_Expected : List Int := [5, 4, 3]

-- Test case 14: Complex tie-breaking scenario
-- Flattened: [10, 20, 30, 20, 30, 40, 30, 40, 50]
-- First occurrence indices: 10→0, 20→1, 30→2, 40→5, 50→8
-- Frequencies: 30→3, 20→2, 40→2, 10→1, 50→1
-- Top 3: 30 (3), 20 (2, wins tie with 40 by first occurrence), 40 (2)
def test14_lists : List (List Int) := [[10, 20, 30], [20, 30, 40], [30, 40, 50]]
def test14_k : Nat := 3
def test14_Expected : List Int := [30, 20, 40]

-- Test case 15: All elements in first list, scattered in others
-- Flattened: [1, 2, 3, 4, 5, 5, 4, 3, 2, 1]
-- First occurrence indices: 1→0, 2→1, 3→2, 4→3, 5→4
-- All frequency 2, sorted by first occurrence
def test15_lists : List (List Int) := [[1, 2, 3, 4, 5], [5], [4], [3], [2], [1]]
def test15_k : Nat := 3
def test15_Expected : List Int := [1, 2, 3]

-- Test case 16: k = 0 edge case
-- When k=0, should return empty list
def test16_lists : List (List Int) := [[1, 2], [3, 4]]
def test16_k : Nat := 0
def test16_Expected : List Int := []

-- Recommend to validate: test cases 0, 1, 2, 4, 6, 9, 16
-- These cover:
-- - Test 0: Problem statement example (required)
-- - Test 1: Clear frequency ordering with tie-breaking
-- - Test 2: All same frequency (pure tie-breaking by first occurrence)
-- - Test 4: Single list edge case
-- - Test 6: Negative numbers with first-occurrence tie-breaking
-- - Test 9: Multiple ties requiring first-occurrence ordering
-- - Test 16: k=0 edge case

end TestCases
