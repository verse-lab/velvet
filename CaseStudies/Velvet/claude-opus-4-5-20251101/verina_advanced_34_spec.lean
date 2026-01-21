import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- longestIncreasingSubsequence: Find the length of the longest strictly increasing subsequence
--
-- Natural language breakdown:
-- 1. Given a list of integers nums, we need to find the longest strictly increasing subsequence
-- 2. A subsequence is a sequence derived from the original list by deleting some or no elements
--    without changing the order of the remaining elements (uses List.Sublist from Mathlib)
-- 3. A strictly increasing sequence means each element is strictly greater than the previous one
-- 4. We return the length of such a longest subsequence
-- 5. For an empty list, the longest increasing subsequence has length 0
-- 6. For a single element list, the length is 1
-- 7. For a list of all identical elements, the length is 1 (only single element is strictly increasing)
-- 8. The result is always non-negative and at most the length of the input list

section Specs

-- Helper: Check if a list is strictly increasing using Mathlib's Pairwise
def isStrictlyIncreasing (l : List Int) : Prop :=
  l.Pairwise (· < ·)

-- Helper: Check if a list is a valid strictly increasing subsequence of nums
def isIncreasingSubseq (subseq : List Int) (nums : List Int) : Prop :=
  subseq.Sublist nums ∧ isStrictlyIncreasing subseq

-- Precondition: No restrictions on the input list
def precondition (nums : List Int) : Prop :=
  True

-- Postcondition clauses
-- 1. Result does not exceed the length of the input list
def ensures1 (nums : List Int) (result : Int) : Prop :=
  result ≤ nums.length

-- 2. There exists a strictly increasing subsequence with exactly this length
def ensures2 (nums : List Int) (result : Int) : Prop :=
  ∃ subseq : List Int, isIncreasingSubseq subseq nums ∧ subseq.length = result.toNat

-- 3. No strictly increasing subsequence has a greater length
def ensures3 (nums : List Int) (result : Int) : Prop :=
  ∀ subseq : List Int, isIncreasingSubseq subseq nums → subseq.length ≤ result.toNat

def postcondition (nums : List Int) (result : Int) : Prop :=
  ensures1 nums result ∧
  ensures2 nums result ∧
  ensures3 nums result

end Specs

section Impl

method longestIncreasingSubsequence (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - [10, 9, 2, 5, 3, 7, 101, 18] has LIS of length 4
-- (e.g., [2, 3, 7, 101] or [2, 5, 7, 18])
def test1_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test1_Expected : Int := 4

-- Test case 2: [0, 1, 0, 3, 2, 3] has LIS of length 4 (e.g., [0, 1, 2, 3])
def test2_nums : List Int := [0, 1, 0, 3, 2, 3]
def test2_Expected : Int := 4

-- Test case 3: All identical elements - only single element subsequence is strictly increasing
def test3_nums : List Int := [7, 7, 7, 7, 7, 7, 7]
def test3_Expected : Int := 1

-- Test case 4: [1, 3, 2, 4] has LIS of length 3 (e.g., [1, 2, 4] or [1, 3, 4])
def test4_nums : List Int := [1, 3, 2, 4]
def test4_Expected : Int := 3

-- Test case 5: Single element list
def test5_nums : List Int := [10]
def test5_Expected : Int := 1

-- Test case 6: Empty list
def test6_nums : List Int := []
def test6_Expected : Int := 0

-- Test case 7: Already strictly increasing list
def test7_nums : List Int := [1, 2, 3, 4, 5]
def test7_Expected : Int := 5

-- Test case 8: Strictly decreasing list - LIS has length 1
def test8_nums : List Int := [5, 4, 3, 2, 1]
def test8_Expected : Int := 1

-- Test case 9: Negative numbers
def test9_nums : List Int := [-3, -2, -1, 0, 1]
def test9_Expected : Int := 5

-- Test case 10: Mixed positive and negative with gaps
def test10_nums : List Int := [-5, 10, -3, 2, 8, 1, 9]
def test10_Expected : Int := 4

-- Recommend to validate: 1, 3, 5

end TestCases
