import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- longestIncreasingSubsequence: Find the length of the longest increasing subsequence
-- Natural language breakdown:
-- 1. Given a list of integers, find the longest increasing subsequence (LIS)
-- 2. A subsequence is obtained by deleting some (possibly zero) elements without changing order
-- 3. An increasing subsequence has elements in strictly increasing order (each element > previous)
-- 4. We need to return the length of the longest such subsequence
-- 5. For empty list, return 0
-- 6. For non-empty list with all equal elements, return 1 (single element is trivially increasing)
-- 7. For strictly decreasing list, return 1 (any single element forms valid subsequence)
-- 8. For strictly increasing list, return list length (entire list is valid subsequence)
--
-- Key properties:
-- - A subsequence preserves relative order but may skip elements
-- - Strictly increasing means each element is strictly greater than the previous
-- - The result is the maximum length over all valid increasing subsequences
-- - Result is always between 0 (empty list) and list length (fully increasing list)

section Specs

register_specdef_allow_recursion

-- Helper: Check if a list of integers is strictly increasing
def isStrictlyIncreasing : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x < y ∧ isStrictlyIncreasing (y :: rest)

-- Helper: Check if one list is a subsequence of another (preserves order, may skip elements)
def isSubsequenceOf : List Int → List Int → Prop
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys => 
    if x = y then isSubsequenceOf xs ys
    else isSubsequenceOf (x :: xs) ys

-- Helper: Check if a list is a valid increasing subsequence of another list
def isIncreasingSubsequenceOf (subseq : List Int) (original : List Int) : Prop :=
  isSubsequenceOf subseq original ∧ isStrictlyIncreasing subseq

-- Precondition: No constraints on input
def precondition (numbers : List Int) : Prop :=
  True

-- Postcondition: result is the length of the longest increasing subsequence
-- Properties:
-- 1. There exists an increasing subsequence of this length
-- 2. No increasing subsequence has greater length
-- 3. Result bounds: 0 for empty list, at least 1 for non-empty, at most list length
def postcondition (numbers : List Int) (result : Nat) : Prop :=
  -- There exists an increasing subsequence of length result
  (∃ subseq : List Int, 
    isIncreasingSubsequenceOf subseq numbers ∧ 
    subseq.length = result) ∧
  -- No increasing subsequence has greater length
  (∀ subseq : List Int, 
    isIncreasingSubsequenceOf subseq numbers → 
    subseq.length ≤ result) ∧
  -- Result is 0 iff list is empty
  (numbers = [] ↔ result = 0)

end Specs

section Impl

method longestIncreasingSubsequence (numbers : List Int)
  return (result : Nat)
  require precondition numbers
  ensures postcondition numbers result
  do
    pure 0

end Impl

section TestCases

-- Test case 1: Standard example with multiple increasing subsequences
-- LIS: [10, 22, 33, 50, 60] has length 5
def test1_numbers : List Int := [10, 22, 9, 33, 21, 50, 41, 60]
def test1_Expected : Nat := 5

-- Test case 2: Another standard example
-- LIS: [3, 10, 20] has length 3
def test2_numbers : List Int := [3, 10, 2, 1, 20]
def test2_Expected : Nat := 3

-- Test case 3: Example with different LIS pattern
-- LIS: [3, 10, 40, 80] has length 4
def test3_numbers : List Int := [50, 3, 10, 7, 40, 80]
def test3_Expected : Nat := 4

-- Test case 4: Strictly decreasing sequence
-- LIS: any single element, length 1
def test4_numbers : List Int := [10, 9, 8, 7, 6, 5, 4, 3, 2, 1]
def test4_Expected : Nat := 1

-- Test case 5: Strictly increasing sequence
-- LIS: entire list [1, 2, 3, 4, 5], length 5
def test5_numbers : List Int := [1, 2, 3, 4, 5]
def test5_Expected : Nat := 5

-- Test case 6: Empty list
-- LIS: empty, length 0
def test6_numbers : List Int := []
def test6_Expected : Nat := 0

-- Test case 7: Single element
-- LIS: [5], length 1
def test7_numbers : List Int := [5]
def test7_Expected : Nat := 1

-- Test case 8: All equal elements (not strictly increasing)
-- LIS: any single element, length 1
def test8_numbers : List Int := [5, 5, 5, 5]
def test8_Expected : Nat := 1

-- Recommend to validate: 1, 5, 6

end TestCases
