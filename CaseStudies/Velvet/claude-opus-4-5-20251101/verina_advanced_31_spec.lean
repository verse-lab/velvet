import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    longestIncreasingSubseqLength: Find the length of the longest strictly increasing subsequence

    Natural language breakdown:
    1. Given a list of integers xs, we need to find the longest strictly increasing subsequence
    2. A subsequence is derived by deleting zero or more elements without changing order
    3. A subsequence is strictly increasing if each element is greater than the previous
    4. We return the length (as Nat) of the longest such subsequence
    5. For an empty list, the result is 0 (no elements means no subsequence)
    6. For a strictly decreasing list, the result is 1 (each single element is an increasing subsequence)
    7. For a strictly increasing list, the result equals the list length
    8. The subsequence relation is captured by List.Sublist (List.Sublist sub xs)
    9. A list is strictly increasing if for all adjacent elements, the previous is less than the next
    10. We need to find the maximum length over all sublists that are strictly increasing
-/

section Specs

register_specdef_allow_recursion

-- Helper: Check if a list is strictly increasing using IsChain from Mathlib
def isStrictlyIncreasing (l : List Int) : Prop :=
  l.IsChain (· < ·)

-- Helper: A list is a valid strictly increasing subsequence of xs
def isIncreasingSubseq (sub : List Int) (xs : List Int) : Prop :=
  List.Sublist sub xs ∧ isStrictlyIncreasing sub

-- Precondition: No restrictions on input
def precondition (xs : List Int) : Prop :=
  True

-- Postcondition:
-- 1. The result is the length of some strictly increasing subsequence of xs
-- 2. No strictly increasing subsequence of xs has length greater than result
-- 3. For empty list, result is 0
def postcondition (xs : List Int) (result : Nat) : Prop :=
  -- There exists a strictly increasing subsequence of length result
  (∃ sub : List Int, isIncreasingSubseq sub xs ∧ sub.length = result) ∧
  -- No strictly increasing subsequence is longer than result
  (∀ sub : List Int, isIncreasingSubseq sub xs → sub.length ≤ result)

end Specs

section Impl

method longestIncreasingSubseqLength (xs : List Int)
  return (result : Nat)
  require precondition xs
  ensures postcondition xs result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Strictly increasing list - entire list is LIS
def test1_xs : List Int := [1, 2, 3, 4]
def test1_Expected : Nat := 4

-- Test case 2: Strictly decreasing list - LIS is any single element
def test2_xs : List Int := [4, 3, 2, 1]
def test2_Expected : Nat := 1

-- Test case 3: Mixed list with LIS of length 4 (e.g., 1, 2, 4, 5 or 1, 3, 4, 5)
def test3_xs : List Int := [1, 3, 2, 4, 0, 5]
def test3_Expected : Nat := 4

-- Test case 4: Empty list - no subsequence possible
def test4_xs : List Int := []
def test4_Expected : Nat := 0

-- Test case 5: Mixed list with LIS of length 3 (e.g., 1, 6, 7 or 5, 6, 7)
def test5_xs : List Int := [5, 1, 6, 2, 7]
def test5_Expected : Nat := 3

-- Test case 6: Single element list
def test6_xs : List Int := [42]
def test6_Expected : Nat := 1

-- Test case 7: Two elements, increasing
def test7_xs : List Int := [1, 2]
def test7_Expected : Nat := 2

-- Test case 8: Two elements, decreasing
def test8_xs : List Int := [2, 1]
def test8_Expected : Nat := 1

-- Test case 9: List with all same elements (no strict increase possible except singles)
def test9_xs : List Int := [3, 3, 3, 3]
def test9_Expected : Nat := 1

-- Test case 10: Longer mixed sequence
def test10_xs : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test10_Expected : Nat := 4

-- Recommend to validate: 1, 3, 9

end TestCases
