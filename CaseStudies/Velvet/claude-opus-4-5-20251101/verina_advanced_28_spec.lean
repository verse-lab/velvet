import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    longestConsecutive: Find the length of the longest sequence of consecutive integers in a list

    Natural language breakdown:
    1. We are given a list of integers with no duplicates
    2. We need to find the longest sequence of consecutive integers that can be formed from elements in the list
    3. Consecutive integers are integers that differ by exactly 1 (e.g., 1, 2, 3, 4)
    4. The elements do not need to appear consecutively in the input list
    5. The result is the length (count) of elements in the longest such sequence
    6. For an empty list, the result is 0
    7. For a single element, the result is 1 (a single element forms a consecutive sequence of length 1)
    8. Example: [100, 4, 200, 1, 3, 2] contains consecutive sequence [1, 2, 3, 4] with length 4

    Key properties:
    - A consecutive sequence starting at integer n with length k contains exactly {n, n+1, ..., n+k-1}
    - The result is the maximum k such that all integers from some n to n+k-1 are present in the list
    - The input list has no duplicates (elements are unique)
-/

section Specs

-- Helper: Check if all integers in range [start, start + len) are in the list
def allInRange (nums : List Int) (start : Int) (len : Nat) : Prop :=
  ∀ i : Nat, i < len → (start + i) ∈ nums

-- Helper: Check if a consecutive sequence of given length starting at start exists in the list
def hasConsecutiveSeq (nums : List Int) (start : Int) (len : Nat) : Prop :=
  allInRange nums start len

-- Precondition: The list has no duplicates
def precondition (nums : List Int) : Prop :=
  nums.Nodup

-- Postcondition:
-- 1. If nums is empty, result is 0
-- 2. If nums is non-empty, result is at least 1
-- 3. There exists a consecutive sequence of length result in nums
-- 4. No consecutive sequence of length greater than result exists in nums
def postcondition (nums : List Int) (result : Nat) : Prop :=
  -- Empty list has result 0
  (nums = [] → result = 0) ∧
  -- Non-empty list has result at least 1
  (nums ≠ [] → result ≥ 1) ∧
  -- There exists a starting point where a consecutive sequence of length result exists
  (result > 0 → ∃ start : Int, hasConsecutiveSeq nums start result) ∧
  -- No longer consecutive sequence exists
  (∀ start : Int, ∀ len : Nat, len > result → ¬hasConsecutiveSeq nums start len)

end Specs

section Impl

method longestConsecutive (nums : List Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - [100, 4, 200, 1, 3, 2] has consecutive sequence [1,2,3,4]
def test1_nums : List Int := [100, 4, 200, 1, 3, 2]
def test1_Expected : Nat := 4

-- Test case 2: Full consecutive sequence [0, 1, 2, 3, 4, 5, 6, 7, 8]
def test2_nums : List Int := [0, 3, 7, 2, 5, 8, 4, 6, 1]
def test2_Expected : Nat := 9

-- Test case 3: Small consecutive sequence [0, 1, 2]
def test3_nums : List Int := [1, 2, 0]
def test3_Expected : Nat := 3

-- Test case 4: Empty list
def test4_nums : List Int := []
def test4_Expected : Nat := 0

-- Test case 5: Single element
def test5_nums : List Int := [10]
def test5_Expected : Nat := 1

-- Test case 6: Two separate elements (no consecutive)
def test6_nums : List Int := [5, 10]
def test6_Expected : Nat := 1

-- Test case 7: Two consecutive elements
def test7_nums : List Int := [5, 6]
def test7_Expected : Nat := 2

-- Test case 8: Negative numbers with consecutive sequence
def test8_nums : List Int := [-3, -1, -2, 0, 1]
def test8_Expected : Nat := 5

-- Test case 9: Multiple separate consecutive sequences, pick longest
def test9_nums : List Int := [1, 2, 3, 10, 11, 12, 13, 14]
def test9_Expected : Nat := 5

-- Test case 10: Large gaps between elements
def test10_nums : List Int := [1, 100, 200, 300]
def test10_Expected : Nat := 1

-- Recommend to validate: 1, 4, 8

end TestCases
