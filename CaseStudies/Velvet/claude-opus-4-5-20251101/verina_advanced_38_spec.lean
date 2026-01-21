import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    maxCoverageAfterRemovingOne: Given a list of intervals, return the maximum span
    that can be achieved after removing exactly one interval.

    Natural language breakdown:
    1. We have a list of intervals, each represented as a pair (start, end) of natural numbers
    2. The list must contain at least one interval
    3. We need to consider removing each interval one at a time
    4. For each removal scenario, we compute the total "span" or "coverage" of the remaining intervals
    5. The span of a set of intervals is the total length covered by their union
    6. We return the maximum span achievable across all possible single-interval removals
    7. When computing coverage, overlapping regions are counted only once
    8. For an interval (a, b), the length is b - a (assuming b >= a)
    9. A point x is covered by an interval (a, b) if a ≤ x < b
    10. The coverage is the cardinality of the set of all natural numbers covered by at least one interval
-/

section Specs

-- Define the set of points covered by a list of intervals
def coveredSet (intervals : List (Nat × Nat)) : Set Nat :=
  {x | ∃ interval ∈ intervals, interval.1 ≤ x ∧ x < interval.2}

-- Remove element at index i from a list
def removeAt (l : List α) (i : Nat) : List α :=
  l.take i ++ l.drop (i + 1)

-- Precondition: at least one interval
def precondition (intervals : List (Nat × Nat)) :=
  intervals.length ≥ 1

-- Postcondition clauses:
-- 1. The result equals the coverage (cardinality of covered set) obtainable by removing some interval
def ensures1 (intervals : List (Nat × Nat)) (result : Nat) :=
  ∃ i : Nat, i < intervals.length ∧ result = Nat.card (coveredSet (removeAt intervals i))

-- 2. The result is at least as large as any coverage after removing any single interval
def ensures2 (intervals : List (Nat × Nat)) (result : Nat) :=
  ∀ i : Nat, i < intervals.length → Nat.card (coveredSet (removeAt intervals i)) ≤ result

def postcondition (intervals : List (Nat × Nat)) (result : Nat) :=
  ensures1 intervals result ∧ ensures2 intervals result

end Specs

section Impl

method maxCoverageAfterRemovingOne (intervals : List (Nat × Nat))
  return (result : Nat)
  require precondition intervals
  ensures postcondition intervals result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: [(1, 3), (2, 5), (6, 8)] - from problem description
-- Removing (1,3): coverage of [(2,5), (6,8)] = 3 + 2 = 5
-- Removing (2,5): coverage of [(1,3), (6,8)] = 2 + 2 = 4
-- Removing (6,8): coverage of [(1,3), (2,5)] = 4 (merged)
-- Maximum = 5
def test1_intervals : List (Nat × Nat) := [(1, 3), (2, 5), (6, 8)]
def test1_Expected : Nat := 5

-- Test case 2: [(1, 4), (2, 6), (8, 10), (9, 12)]
-- Removing one interval, max coverage = 8
def test2_intervals : List (Nat × Nat) := [(1, 4), (2, 6), (8, 10), (9, 12)]
def test2_Expected : Nat := 8

-- Test case 3: [(1, 2), (2, 3), (3, 4)] - consecutive intervals
-- Removing any one gives coverage of 2
def test3_intervals : List (Nat × Nat) := [(1, 2), (2, 3), (3, 4)]
def test3_Expected : Nat := 2

-- Test case 4: [(1, 10), (2, 3), (4, 5)] - one large interval containing others
-- Removing the large interval: coverage = 1 + 1 = 2
-- Removing small intervals: coverage = 9
-- Maximum = 9
def test4_intervals : List (Nat × Nat) := [(1, 10), (2, 3), (4, 5)]
def test4_Expected : Nat := 9

-- Test case 5: [(5, 6), (1, 2), (3, 4)] - unsorted disjoint intervals
-- Each interval has length 1, removing any gives coverage 2
def test5_intervals : List (Nat × Nat) := [(5, 6), (1, 2), (3, 4)]
def test5_Expected : Nat := 2

-- Test case 6: Single interval - removing it gives 0 coverage (edge case)
def test6_intervals : List (Nat × Nat) := [(1, 5)]
def test6_Expected : Nat := 0

-- Test case 7: Two completely overlapping intervals
-- [(1, 5), (1, 5)] - removing one still gives coverage 4
def test7_intervals : List (Nat × Nat) := [(1, 5), (1, 5)]
def test7_Expected : Nat := 4

-- Test case 8: Two adjacent intervals
-- [(1, 3), (3, 5)] - removing (1,3) gives 2, removing (3,5) gives 2
def test8_intervals : List (Nat × Nat) := [(1, 3), (3, 5)]
def test8_Expected : Nat := 2

-- Test case 9: Multiple overlapping intervals
-- [(0, 4), (1, 3), (2, 6)] - all overlap significantly
-- Removing (0,4): coverage of [(1,3), (2,6)] merged = 5
-- Removing (1,3): coverage of [(0,4), (2,6)] merged = 6
-- Removing (2,6): coverage of [(0,4), (1,3)] merged = 4
-- Maximum = 6
def test9_intervals : List (Nat × Nat) := [(0, 4), (1, 3), (2, 6)]
def test9_Expected : Nat := 6

-- Test case 10: Partially overlapping intervals in different order
-- [(2, 7), (1, 4), (5, 9)]
-- Removing (2,7): [(1,4), (5,9)] = 3 + 4 = 7
-- Removing (1,4): [(2,7), (5,9)] merged = 7
-- Removing (5,9): [(2,7), (1,4)] merged = 6
-- Maximum = 7
def test10_intervals : List (Nat × Nat) := [(2, 7), (1, 4), (5, 9)]
def test10_Expected : Nat := 7

-- Recommend to validate: 1, 6, 9

end TestCases
