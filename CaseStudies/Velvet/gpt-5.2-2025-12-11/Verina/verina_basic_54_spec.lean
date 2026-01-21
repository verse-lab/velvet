import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    CanyonSearch: minimum absolute difference between an element of two sorted nonempty integer arrays
    Natural language breakdown:
    1. We are given two arrays `a` and `b` of integers.
    2. Each array is sorted in non-decreasing order.
    3. Each array is non-empty.
    4. Consider all pairs of indices (i,j) with i in bounds of `a` and j in bounds of `b`.
    5. For each pair, compute the absolute difference between the two integers: |a[i] - b[j]|.
    6. Convert this absolute difference to a natural number using `Int.natAbs`.
    7. The output is the minimum such natural number among all pairs.
    8. The result must be achievable by some pair and be less than or equal to every pairwise distance.
    9. Sorting is part of the assumptions; it is not required for the mathematical meaning of the minimum.
-/

section Specs

-- Helper: array is sorted in non-decreasing order
-- (Uses Nat indices and guarded access, as required.)
def isSortedNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: Nat-valued absolute difference between two integers
-- We use `Int.natAbs` so the result is a `Nat`.
def natAbsDiff (x : Int) (y : Int) : Nat :=
  Int.natAbs (x - y)

-- Helper: a value is a minimal element among all pairwise distances between two arrays.
def isMinPairwiseAbsDiff (a : Array Int) (b : Array Int) (d : Nat) : Prop :=
  (∃ (i : Nat) (j : Nat), i < a.size ∧ j < b.size ∧ natAbsDiff a[i]! b[j]! = d) ∧
  (∀ (i : Nat) (j : Nat), i < a.size → j < b.size → d ≤ natAbsDiff a[i]! b[j]!)

-- Preconditions
-- Arrays are non-empty and sorted in non-decreasing order.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧
  b.size > 0 ∧
  isSortedNondecreasing a ∧
  isSortedNondecreasing b

-- Postcondition
-- The result is the minimum Nat absolute difference across all pairs (i,j).
def postcondition (a : Array Int) (b : Array Int) (result : Nat) : Prop :=
  isMinPairwiseAbsDiff a b result

end Specs

section Impl

method CanyonSearch (a : Array Int) (b : Array Int)
  return (result : Nat)
  require precondition a b
  ensures postcondition a b result
  do
    pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: example from prompt
-- a = [1,3,5], b = [2,4,6] => minimum distance is 1

def test1_a : Array Int := #[1, 3, 5]

def test1_b : Array Int := #[2, 4, 6]

def test1_Expected : Nat := 1

-- Test case 2: negative and nonnegative values
-- a = [-5,-2,0], b = [1,3] => minimum distance is 1 (0 vs 1)

def test2_a : Array Int := #[-5, -2, 0]

def test2_b : Array Int := #[1, 3]

def test2_Expected : Nat := 1

-- Test case 3: disjoint ranges with gaps
-- a = [10,20,30], b = [5,15,25] => minimum distance is 5

def test3_a : Array Int := #[10, 20, 30]

def test3_b : Array Int := #[5, 15, 25]

def test3_Expected : Nat := 5

-- Test case 4: exact match across arrays yields zero
-- a contains 3 and b = [3] => minimum distance is 0

def test4_a : Array Int := #[1, 2, 3, 4, 5]

def test4_b : Array Int := #[3]

def test4_Expected : Nat := 0

-- Test case 5: mixed negatives/positives; closest are -5 and -3 (distance 2)

def test5_a : Array Int := #[-10, -5, 0, 5, 10]

def test5_b : Array Int := #[-3, 2, 8]

def test5_Expected : Nat := 2

-- Test case 6: both arrays size 1
-- |(-7) - (4)| = 11

def test6_a : Array Int := #[-7]

def test6_b : Array Int := #[4]

def test6_Expected : Nat := 11

-- Test case 7: duplicates inside arrays; still minimum computed across all pairs
-- a = [1,1,1], b = [2,2] => minimum is 1

def test7_a : Array Int := #[1, 1, 1]

def test7_b : Array Int := #[2, 2]

def test7_Expected : Nat := 1

-- Test case 8: identical constant arrays => minimum is 0

def test8_a : Array Int := #[0, 0, 0]

def test8_b : Array Int := #[0]

def test8_Expected : Nat := 0

-- Test case 9: larger spread, closest pair near middle
-- a = [-100, -50, 0, 50], b = [-60, 10, 70] => min is 10 (|-50 - -60|)

def test9_a : Array Int := #[-100, -50, 0, 50]

def test9_b : Array Int := #[-60, 10, 70]

def test9_Expected : Nat := 10

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 4, 6

end TestCases
