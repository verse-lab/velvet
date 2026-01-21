import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- lengthOfLIS: Determine the length of the longest strictly increasing subsequence in an array
--
-- Natural language breakdown:
-- 1. Given a list of integers, find the longest strictly increasing subsequence
-- 2. A subsequence is derived by deleting some or no elements without changing order
-- 3. Strictly increasing means each element is greater than the previous one
-- 4. We need to return the length of this longest subsequence
-- 5. Key properties:
--    a. A subsequence preserves the relative order of elements from the original list
--    b. The subsequence elements must be strictly increasing (a[i] < a[j] for i < j)
--    c. We want the maximum length among all such subsequences
-- 6. Edge cases:
--    - Empty list: length is 0
--    - Single element: length is 1
--    - All equal elements: length is 1
--    - Already sorted increasing: length is the list length
--    - Strictly decreasing: length is 1

section Specs

register_specdef_allow_recursion

-- Helper: Check if a list is strictly increasing
def isStrictlyIncreasing (l : List Int) : Prop :=
  ∀ i : Nat, i + 1 < l.length → l[i]! < l[i + 1]!

-- Helper: Check if one list is a subsequence of another (preserves order, not necessarily contiguous)
-- A subsequence can be obtained by deleting some elements from the original list
def isSubseqOf (sub : List Int) (main : List Int) : Prop :=
  sub.Sublist main

-- Helper: Check if a list is a valid strictly increasing subsequence of the given list
def isIncreasingSubseqOf (sub : List Int) (main : List Int) : Prop :=
  isSubseqOf sub main ∧ isStrictlyIncreasing sub

-- Precondition: no specific requirements on input
def precondition (nums : List Int) : Prop :=
  True

-- Postcondition: result is the length of the longest strictly increasing subsequence
-- 1. There exists a strictly increasing subsequence of nums with length equal to result
-- 2. No strictly increasing subsequence of nums has length greater than result
def postcondition (nums : List Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ sub : List Int, isIncreasingSubseqOf sub nums ∧ sub.length = result.toNat) ∧
  (∀ sub : List Int, isIncreasingSubseqOf sub nums → sub.length ≤ result.toNat)

end Specs

section Impl

method lengthOfLIS (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - [10, 9, 2, 5, 3, 7, 101, 18]
-- LIS could be [2, 3, 7, 101] or [2, 3, 7, 18] or [2, 5, 7, 101] etc., all length 4
def test1_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test1_Expected : Int := 4

-- Test case 2: [0, 1, 0, 3, 2, 3] - LIS is [0, 1, 2, 3] with length 4
def test2_nums : List Int := [0, 1, 0, 3, 2, 3]
def test2_Expected : Int := 4

-- Test case 3: All equal elements [7, 7, 7, 7, 7, 7, 7] - LIS length is 1
def test3_nums : List Int := [7, 7, 7, 7, 7, 7, 7]
def test3_Expected : Int := 1

-- Test case 4: [4, 10, 4, 3, 8, 9] - LIS could be [4, 8, 9] with length 3
def test4_nums : List Int := [4, 10, 4, 3, 8, 9]
def test4_Expected : Int := 3

-- Test case 5: [1, 3, 6, 7, 9, 4, 10, 5, 6] - LIS is [1, 3, 6, 7, 9, 10] with length 6
def test5_nums : List Int := [1, 3, 6, 7, 9, 4, 10, 5, 6]
def test5_Expected : Int := 6

-- Test case 6: Empty list - LIS length is 0
def test6_nums : List Int := []
def test6_Expected : Int := 0

-- Test case 7: Single element - LIS length is 1
def test7_nums : List Int := [5]
def test7_Expected : Int := 1

-- Test case 8: Already strictly increasing [1, 2, 3, 4, 5] - LIS is entire list
def test8_nums : List Int := [1, 2, 3, 4, 5]
def test8_Expected : Int := 5

-- Test case 9: Strictly decreasing [5, 4, 3, 2, 1] - LIS length is 1
def test9_nums : List Int := [5, 4, 3, 2, 1]
def test9_Expected : Int := 1

-- Test case 10: Two elements increasing
def test10_nums : List Int := [1, 2]
def test10_Expected : Int := 2

-- Recommend to validate: 1, 3, 6

end TestCases
