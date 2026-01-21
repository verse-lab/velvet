import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    lengthOfLIS: Find the length of the longest strictly increasing subsequence
    Natural language breakdown:
    1. Given a list of integers, find the length of the longest strictly increasing subsequence
    2. A subsequence is derived by deleting some or no elements without changing the order
    3. A strictly increasing subsequence has each element greater than the previous
    4. The result is the maximum length among all such subsequences
    5. For an empty list, the length is 0
    6. For a list with all equal elements, the length is 1 (single element is trivially increasing)
    7. Key properties:
       a. A subsequence preserves the relative order of elements from the original list
       b. Strictly increasing means each element is strictly greater than its predecessor
       c. We want the maximum length, not the subsequence itself
    8. Edge cases:
       - Empty list: result is 0
       - Single element: result is 1
       - All equal elements: result is 1
       - Already sorted in increasing order: result is the list length
       - Sorted in decreasing order: result is 1
-/

section Specs

-- Helper: Check if a list is strictly increasing using Mathlib's Pairwise
def isStrictlyIncreasing (l : List Int) : Prop :=
  l.Pairwise (· < ·)

-- Helper: Check if one list is a subsequence of another using Mathlib's Sublist
-- A subsequence preserves relative order (can delete elements but not reorder)
def isStrictlyIncreasingSubseq (sub : List Int) (original : List Int) : Prop :=
  sub.Sublist original ∧ isStrictlyIncreasing sub

-- Postcondition clauses
-- 1. The result is achievable: there exists a strictly increasing subsequence of that length
def ensures1 (nums : List Int) (result : Nat) : Prop :=
  ∃ sub : List Int, isStrictlyIncreasingSubseq sub nums ∧ sub.length = result

-- 2. The result is maximal: no strictly increasing subsequence has greater length
def ensures2 (nums : List Int) (result : Nat) : Prop :=
  ∀ sub : List Int, isStrictlyIncreasingSubseq sub nums → sub.length ≤ result

def precondition (nums : List Int) : Prop :=
  True  -- no preconditions needed

def postcondition (nums : List Int) (result : Nat) : Prop :=
  ensures1 nums result ∧ ensures2 nums result

end Specs

section Impl

method lengthOfLIS (nums : List Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: Example from problem - mixed sequence with LIS [2, 3, 7, 101] or [2, 5, 7, 101] etc.
def test1_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test1_Expected : Nat := 4

-- Test case 2: Sequence with multiple paths to same length
def test2_nums : List Int := [0, 1, 0, 3, 2, 3]
def test2_Expected : Nat := 4

-- Test case 3: All equal elements - only single element subsequences are strictly increasing
def test3_nums : List Int := [7, 7, 7, 7, 7, 7, 7]
def test3_Expected : Nat := 1

-- Test case 4: Empty list - edge case
def test4_nums : List Int := []
def test4_Expected : Nat := 0

-- Test case 5: Mixed sequence with shorter LIS
def test5_nums : List Int := [4, 10, 4, 3, 8, 9]
def test5_Expected : Nat := 3

-- Test case 6: Longer increasing sequence with some disruptions
def test6_nums : List Int := [1, 3, 6, 7, 9, 4, 10, 5, 6]
def test6_Expected : Nat := 6

-- Test case 7: Classic LIS example
def test7_nums : List Int := [10, 22, 9, 33, 21, 50, 41, 60, 80]
def test7_Expected : Nat := 6

-- Test case 8: Classic 16-element example
def test8_nums : List Int := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
def test8_Expected : Nat := 6

-- Test case 9: Negative numbers - simple increasing pair
def test9_nums : List Int := [-2, -1]
def test9_Expected : Nat := 2

-- Recommend to validate: 1, 3, 4

end TestCases
