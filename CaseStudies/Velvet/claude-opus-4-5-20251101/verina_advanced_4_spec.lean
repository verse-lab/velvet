import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    LongestIncreasingSubsequence: Find the length of the longest strictly increasing subsequence
    Natural language breakdown:
    1. Given an array of integers, find the longest subsequence where each element is strictly less than the next
    2. A subsequence is obtained by deleting some (possibly zero) elements from the array without changing the order of remaining elements
    3. "Strictly increasing" means each element is strictly less than the following element (not ≤, but <)
    4. We return the length of this longest increasing subsequence
    5. Examples:
       - [5, 2, 8, 6, 3, 6, 9, 7] → LIS could be [2, 3, 6, 9] with length 4
       - [3, 1, 2, 1, 0] → LIS could be [1, 2] with length 2
       - [] → Empty array has LIS of length 0
    6. Key properties:
       - A subsequence preserves relative order from the original array
       - The result is the maximum length over all possible strictly increasing subsequences
       - For empty array, result is 0
       - For any non-empty array, result is at least 1 (single element is trivially increasing)
-/

section Specs

-- Check if a list is strictly increasing using Mathlib's List.Chain'
-- This avoids explicit recursion
def isStrictlyIncreasing (sub : List Int) : Prop :=
  List.Chain' (· < ·) sub

-- Check if one list is a subsequence of another (preserves order, allows gaps)
-- Using Mathlib's List.Sublist
def isIncreasingSubseqOf (sub : List Int) (arr : Array Int) : Prop :=
  sub.Sublist arr.toList ∧ isStrictlyIncreasing sub

-- Precondition: no restrictions on input array
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is the length of the longest increasing subsequence
-- 1. Result is non-negative
-- 2. There exists an increasing subsequence of that length
-- 3. No increasing subsequence has length greater than result
def postcondition (a : Array Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ sub : List Int, isIncreasingSubseqOf sub a ∧ sub.length = result.toNat) ∧
  (∀ sub : List Int, isIncreasingSubseqOf sub a → sub.length ≤ result.toNat)

end Specs

section Impl

method LongestIncreasingSubsequence (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - mixed array with LIS of length 4
def test1_a : Array Int := #[5, 2, 8, 6, 3, 6, 9, 7]
def test1_Expected : Int := 4

-- Test case 2: Decreasing-ish array with small LIS
def test2_a : Array Int := #[3, 1, 2, 1, 0]
def test2_Expected : Int := 2

-- Test case 3: Longer array with LIS of length 6
def test3_a : Array Int := #[2, 3, -2, -1, 7, 19, 3, 6, -4, 6, -7, 0, 9, 12, 10]
def test3_Expected : Int := 6

-- Test case 4: Mixed array with negative numbers
def test4_a : Array Int := #[5, -5, -3, 2, 4, 1, 0, -1, 3, 2, 0]
def test4_Expected : Int := 4

-- Test case 5: Array with various patterns
def test5_a : Array Int := #[1, 7, 23, 14, -4, 21, 8, 2, -1, 9, 12, 2]
def test5_Expected : Int := 5

-- Test case 6: Empty array - edge case
def test6_a : Array Int := #[]
def test6_Expected : Int := 0

-- Test case 7: Single element array
def test7_a : Array Int := #[42]
def test7_Expected : Int := 1

-- Test case 8: Already sorted increasing array
def test8_a : Array Int := #[1, 2, 3, 4, 5]
def test8_Expected : Int := 5

-- Test case 9: All same elements
def test9_a : Array Int := #[5, 5, 5, 5]
def test9_Expected : Int := 1

-- Test case 10: Strictly decreasing array
def test10_a : Array Int := #[5, 4, 3, 2, 1]
def test10_Expected : Int := 1

-- Recommend to validate: 1, 6, 8

end TestCases
