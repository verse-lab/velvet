import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    CanyonSearch: Find the minimum absolute difference between any pair of integers,
    where one integer is from the first sorted array and the other is from the second sorted array.
    
    Natural language breakdown:
    1. We have two arrays of integers, both sorted in non-decreasing order
    2. Both arrays are guaranteed to be non-empty
    3. We need to find the minimum absolute difference |a[i] - b[j]| for all valid i, j
    4. The result is a natural number (Nat) representing this minimum difference
    5. Key properties:
       a. The result must be achievable: there exist indices i, j such that |a[i] - b[j]| equals the result
       b. The result must be minimal: for all indices i, j, the result is ≤ |a[i] - b[j]|
    6. Edge cases to consider:
       - Arrays with common elements: minimum difference is 0
       - Arrays with no overlap: minimum is the smallest gap between elements
       - Single element arrays: straightforward comparison
    7. The sorted property of arrays can be exploited for efficient computation,
       but the specification focuses on the correctness criteria, not the algorithm
-/

section Specs

-- Helper: compute absolute difference between two integers as a natural number
def absDiff (x : Int) (y : Int) : Nat := (x - y).natAbs

-- Helper: check if a value is achievable as a difference between some pair
def isAchievableDiff (a : Array Int) (b : Array Int) (val : Nat) : Prop :=
  ∃ i j, i < a.size ∧ j < b.size ∧ absDiff a[i]! b[j]! = val

-- Helper: check if a value is minimal among all pairwise differences
def isMinimalDiff (a : Array Int) (b : Array Int) (val : Nat) : Prop :=
  ∀ i j, i < a.size → j < b.size → val ≤ absDiff a[i]! b[j]!

-- Helper: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j, i ≤ j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition clauses
def require1 (a : Array Int) (b : Array Int) :=
  a.size > 0  -- First array is non-empty

def require2 (a : Array Int) (b : Array Int) :=
  b.size > 0  -- Second array is non-empty

def require3 (a : Array Int) (b : Array Int) :=
  isSortedNonDecreasing a  -- First array is sorted

def require4 (a : Array Int) (b : Array Int) :=
  isSortedNonDecreasing b  -- Second array is sorted

-- Postcondition clauses
def ensures1 (a : Array Int) (b : Array Int) (result : Nat) :=
  isAchievableDiff a b result  -- Result is achievable

def ensures2 (a : Array Int) (b : Array Int) (result : Nat) :=
  isMinimalDiff a b result  -- Result is minimal

def precondition (a : Array Int) (b : Array Int) :=
  require1 a b ∧ require2 a b ∧ require3 a b ∧ require4 a b

def postcondition (a : Array Int) (b : Array Int) (result : Nat) :=
  ensures1 a b result ∧ ensures2 a b result

end Specs

section Impl

method CanyonSearch (a : Array Int) (b : Array Int)
  return (result : Nat)
  require precondition a b
  ensures postcondition a b result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Basic interleaved arrays
def test1_a : Array Int := #[1, 3, 5]
def test1_b : Array Int := #[2, 4, 6]
def test1_Expected : Nat := 1

-- Test case 2: Arrays with negative numbers
def test2_a : Array Int := #[-5, -2, 0]
def test2_b : Array Int := #[1, 3]
def test2_Expected : Nat := 1

-- Test case 3: Larger gap between arrays
def test3_a : Array Int := #[10, 20, 30]
def test3_b : Array Int := #[5, 15, 25]
def test3_Expected : Nat := 5

-- Test case 4: Common element (zero difference)
def test4_a : Array Int := #[1, 2, 3, 4, 5]
def test4_b : Array Int := #[3]
def test4_Expected : Nat := 0

-- Test case 5: Mixed positive and negative with varying gaps
def test5_a : Array Int := #[-10, -5, 0, 5, 10]
def test5_b : Array Int := #[-3, 2, 8]
def test5_Expected : Nat := 2

-- Test case 6: Single element arrays
def test6_a : Array Int := #[7]
def test6_b : Array Int := #[12]
def test6_Expected : Nat := 5

-- Test case 7: Identical arrays
def test7_a : Array Int := #[1, 2, 3]
def test7_b : Array Int := #[1, 2, 3]
def test7_Expected : Nat := 0

-- Test case 8: Non-overlapping arrays with large gap
def test8_a : Array Int := #[1, 2, 3]
def test8_b : Array Int := #[100, 200, 300]
def test8_Expected : Nat := 97

-- Test case 9: Arrays with single common boundary
def test9_a : Array Int := #[1, 5, 10]
def test9_b : Array Int := #[10, 15, 20]
def test9_Expected : Nat := 0

-- Test case 10: All negative numbers
def test10_a : Array Int := #[-100, -50, -25]
def test10_b : Array Int := #[-30, -20, -10]
def test10_Expected : Nat := 5

-- Recommend to validate: 1, 4, 5

end TestCases
