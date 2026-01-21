import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    mergeIntervals: Merge all overlapping intervals from a given list of intervals.

    Natural language breakdown:
    1. Each interval is represented as a pair (start, end) where start ≤ end
    2. Two intervals overlap if one starts before or when the other ends (i.e., start1 ≤ end2 and start2 ≤ end1)
    3. Overlapping intervals should be merged into a single interval spanning from the minimum start to the maximum end
    4. The output should be a list of non-overlapping intervals
    5. The output intervals should be sorted by their start times
    6. The output intervals should cover exactly the same points as the union of all input intervals
    7. Adjacent intervals that touch (e.g., (1,4) and (4,5)) should also be merged
    8. The result should have no redundant intervals (each merged interval is maximal)
-/

section Specs

-- A point x is covered by an interval (a, b) if a ≤ x ≤ b
def pointInInterval (x : Int) (interval : Int × Int) : Prop :=
  interval.1 ≤ x ∧ x ≤ interval.2

-- A point x is covered by a list of intervals if it's in at least one of them
def pointCoveredByList (x : Int) (intervals : List (Int × Int)) : Prop :=
  ∃ interval ∈ intervals, pointInInterval x interval

-- Two intervals are disjoint (non-overlapping) if they don't share any points and don't touch
def intervalsDisjoint (i1 : Int × Int) (i2 : Int × Int) : Prop :=
  i2.1 > i1.2 ∨ i1.1 > i2.2

-- An interval is valid if start ≤ end
def validInterval (interval : Int × Int) : Prop :=
  interval.1 ≤ interval.2

-- All intervals in a list are valid
def allValid (intervals : List (Int × Int)) : Prop :=
  ∀ interval ∈ intervals, validInterval interval

-- The result intervals are pairwise disjoint and separated (no touching)
def pairwiseDisjoint (intervals : List (Int × Int)) : Prop :=
  ∀ i : Nat, ∀ j : Nat, i < intervals.length → j < intervals.length → i ≠ j →
    intervalsDisjoint intervals[i]! intervals[j]!

-- The result is sorted by start times with strict separation
def sortedByStart (intervals : List (Int × Int)) : Prop :=
  ∀ i : Nat, ∀ j : Nat, i < j → j < intervals.length →
    intervals[i]!.2 < intervals[j]!.1

-- Precondition: all input intervals are valid
def precondition (intervals : List (Int × Int)) :=
  allValid intervals

-- Postcondition clauses
-- 1. All result intervals are valid
def ensures1 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  allValid result

-- 2. Coverage preservation: every point covered by input is covered by result
def ensures2 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  ∀ x : Int, pointCoveredByList x intervals → pointCoveredByList x result

-- 3. No extra coverage: every point covered by result is covered by input
def ensures3 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  ∀ x : Int, pointCoveredByList x result → pointCoveredByList x intervals

-- 4. Result intervals are sorted by start time with gaps between them
def ensures4 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  sortedByStart result

-- 5. Result intervals are pairwise disjoint (non-overlapping)
def ensures5 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  pairwiseDisjoint result

def postcondition (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  ensures1 intervals result ∧
  ensures2 intervals result ∧
  ensures3 intervals result ∧
  ensures4 intervals result ∧
  ensures5 intervals result

end Specs

section Impl

method mergeIntervals (intervals : List (Int × Int))
  return (result : List (Int × Int))
  require precondition intervals
  ensures postcondition intervals result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Example from problem - multiple overlapping and non-overlapping intervals
def test1_intervals : List (Int × Int) := [(1, 3), (2, 6), (8, 10), (15, 18)]
def test1_Expected : List (Int × Int) := [(1, 6), (8, 10), (15, 18)]

-- Test case 2: Two touching intervals should merge
def test2_intervals : List (Int × Int) := [(1, 4), (4, 5)]
def test2_Expected : List (Int × Int) := [(1, 5)]

-- Test case 3: One interval contains others
def test3_intervals : List (Int × Int) := [(1, 10), (2, 3), (4, 5)]
def test3_Expected : List (Int × Int) := [(1, 10)]

-- Test case 4: No overlapping intervals
def test4_intervals : List (Int × Int) := [(1, 2), (3, 4), (5, 6)]
def test4_Expected : List (Int × Int) := [(1, 2), (3, 4), (5, 6)]

-- Test case 5: Unsorted input with overlapping intervals
def test5_intervals : List (Int × Int) := [(5, 6), (1, 3), (2, 4)]
def test5_Expected : List (Int × Int) := [(1, 4), (5, 6)]

-- Test case 6: Empty input
def test6_intervals : List (Int × Int) := []
def test6_Expected : List (Int × Int) := []

-- Test case 7: Single interval
def test7_intervals : List (Int × Int) := [(3, 7)]
def test7_Expected : List (Int × Int) := [(3, 7)]

-- Test case 8: All intervals merge into one
def test8_intervals : List (Int × Int) := [(1, 2), (2, 3), (3, 4), (4, 5)]
def test8_Expected : List (Int × Int) := [(1, 5)]

-- Test case 9: Negative numbers
def test9_intervals : List (Int × Int) := [(-5, -2), (-3, 0), (1, 3)]
def test9_Expected : List (Int × Int) := [(-5, 0), (1, 3)]

-- Test case 10: Same interval repeated
def test10_intervals : List (Int × Int) := [(2, 5), (2, 5), (2, 5)]
def test10_Expected : List (Int × Int) := [(2, 5)]

-- Recommend to validate: 1, 2, 5

end TestCases
