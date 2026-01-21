import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    longestIncreasingStreak: Compute the length of the longest strictly increasing contiguous subarray
    Natural language breakdown:
    1. We have a list of integers as input
    2. A contiguous subarray is a sequence of consecutive elements from the list
    3. A strictly increasing subarray is one where each element is strictly greater than the previous one
    4. We need to find the maximum length among all such strictly increasing contiguous subarrays
    5. If the list is empty, the result should be 0
    6. If no element is strictly greater than its predecessor (e.g., all equal or decreasing), 
       each single element forms a streak of length 1
    7. Key properties:
       a. The result is 0 if and only if the list is empty
       b. The result is at least 1 if the list is non-empty
       c. The result is at most the length of the list
       d. There exists a contiguous subarray of the result length that is strictly increasing
       e. No contiguous subarray of length greater than the result is strictly increasing
-/

section Specs

-- Helper: Check if a subarray from index start with given length is strictly increasing
def isStrictlyIncreasingSubarray (nums : List Int) (start : Nat) (len : Nat) : Prop :=
  start + len ≤ nums.length ∧
  len ≥ 1 ∧
  ∀ i : Nat, i + 1 < len → nums[start + i]! < nums[start + i + 1]!

-- Helper: Check if there exists a strictly increasing contiguous subarray of given length
def existsStrictlyIncreasingOfLength (nums : List Int) (len : Nat) : Prop :=
  ∃ start : Nat, isStrictlyIncreasingSubarray nums start len

-- Helper: No strictly increasing contiguous subarray exists with length greater than given value
def noLongerStrictlyIncreasing (nums : List Int) (maxLen : Nat) : Prop :=
  ∀ len : Nat, len > maxLen → ¬existsStrictlyIncreasingOfLength nums len

-- Precondition: No constraints on input
def precondition (nums : List Int) : Prop :=
  True

-- Postcondition: result is the length of the longest strictly increasing contiguous subarray
def postcondition (nums : List Int) (result : Nat) : Prop :=
  -- Empty list case
  (nums.length = 0 → result = 0) ∧
  -- Non-empty list case: result is at least 1
  (nums.length > 0 → result ≥ 1) ∧
  -- Result cannot exceed list length
  result ≤ nums.length ∧
  -- There exists a strictly increasing subarray of length result (if non-empty)
  (nums.length > 0 → existsStrictlyIncreasingOfLength nums result) ∧
  -- No longer strictly increasing subarray exists
  noLongerStrictlyIncreasing nums result

end Specs

section Impl

method longestIncreasingStreak (nums : List Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - mixed increasing and decreasing
def test1_nums : List Int := [1, 2, 3, 2, 4, 5, 6]
def test1_Expected : Nat := 4

-- Test case 2: Entire list is strictly increasing
def test2_nums : List Int := [10, 20, 30, 40]
def test2_Expected : Nat := 4

-- Test case 3: All elements are equal - each forms streak of 1
def test3_nums : List Int := [5, 5, 5, 5]
def test3_Expected : Nat := 1

-- Test case 4: Strictly decreasing list - each forms streak of 1
def test4_nums : List Int := [10, 9, 8, 7]
def test4_Expected : Nat := 1

-- Test case 5: Empty list
def test5_nums : List Int := []
def test5_Expected : Nat := 0

-- Test case 6: Multiple increasing streaks, longest at end
def test6_nums : List Int := [1, 2, 1, 2, 3, 0, 1, 2, 3, 4]
def test6_Expected : Nat := 5

-- Test case 7: Single element list
def test7_nums : List Int := [42]
def test7_Expected : Nat := 1

-- Test case 8: Two elements increasing
def test8_nums : List Int := [1, 2]
def test8_Expected : Nat := 2

-- Test case 9: Two elements equal
def test9_nums : List Int := [3, 3]
def test9_Expected : Nat := 1

-- Test case 10: Negative numbers with increasing streak
def test10_nums : List Int := [-5, -3, -1, 0, 2, 1, 3]
def test10_Expected : Nat := 5

-- Recommend to validate: 1, 5, 6

end TestCases
