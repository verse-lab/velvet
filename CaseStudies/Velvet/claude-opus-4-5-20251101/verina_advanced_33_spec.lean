import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    longestIncreasingSubsequence: Find the length of the longest strictly increasing subsequence
    
    Natural language breakdown:
    1. Given a list of integers, we need to find the longest strictly increasing subsequence
    2. A subsequence is formed by deleting zero or more elements without changing the relative order
    3. "Strictly increasing" means each element is strictly greater than the previous one
    4. We return the length of such longest subsequence
    5. If the list is empty, return 0
    6. If all elements are the same, the longest increasing subsequence has length 1
    7. Key properties:
       a. The result is a natural number between 0 and the length of the input list
       b. For non-empty lists, the result is at least 1 (single element is trivially increasing)
       c. The result equals the maximum length over all strictly increasing subsequences
    8. Examples:
       - [10, 9, 2, 5, 3, 7, 101, 18] → 4 (e.g., [2, 3, 7, 101] or [2, 5, 7, 101])
       - [0, 1, 0, 3, 2, 3] → 4 (e.g., [0, 1, 2, 3])
       - [7, 7, 7, 7, 7] → 1 (any single 7)
       - [] → 0
-/

section Specs

-- Helper: Check if a list is strictly increasing (non-recursive, using quantifiers)
def isStrictlyIncreasing (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! < l[j]!

-- Helper: The result is the maximum length among all strictly increasing subsequences
-- Uses List.Sublist from Mathlib to define subsequence relationship
def isLongestIncreasingSubsequenceLength (nums : List Int) (len : Nat) : Prop :=
  -- There exists a strictly increasing subsequence of this length
  (∃ subseq : List Int, subseq.Sublist nums ∧ isStrictlyIncreasing subseq ∧ subseq.length = len) ∧
  -- No strictly increasing subsequence has greater length
  (∀ subseq : List Int, subseq.Sublist nums → isStrictlyIncreasing subseq → subseq.length ≤ len)

def precondition (nums : List Int) : Prop :=
  True  -- no preconditions

def postcondition (nums : List Int) (result : Nat) : Prop :=
  -- For empty list, result is 0
  (nums = [] → result = 0) ∧
  -- For non-empty list, result is the length of longest strictly increasing subsequence
  (nums ≠ [] → isLongestIncreasingSubsequenceLength nums result)

end Specs

section Impl

method longestIncreasingSubsequence (nums : List Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: Example from problem description
def test1_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test1_Expected : Nat := 4

-- Test case 2: Another example with duplicates
def test2_nums : List Int := [0, 1, 0, 3, 2, 3]
def test2_Expected : Nat := 4

-- Test case 3: All elements are the same
def test3_nums : List Int := [7, 7, 7, 7, 7]
def test3_Expected : Nat := 1

-- Test case 4: Empty list
def test4_nums : List Int := []
def test4_Expected : Nat := 0

-- Test case 5: Mixed values
def test5_nums : List Int := [4, 10, 4, 3, 8, 9]
def test5_Expected : Nat := 3

-- Test case 6: Already sorted (increasing)
def test6_nums : List Int := [1, 2, 3, 4, 5]
def test6_Expected : Nat := 5

-- Test case 7: Decreasing order
def test7_nums : List Int := [5, 4, 3, 2, 1]
def test7_Expected : Nat := 1

-- Test case 8: Single element
def test8_nums : List Int := [42]
def test8_Expected : Nat := 1

-- Test case 9: Two elements increasing
def test9_nums : List Int := [1, 2]
def test9_Expected : Nat := 2

-- Test case 10: Negative numbers
def test10_nums : List Int := [-5, -2, 0, 3, 1, 4]
def test10_Expected : Nat := 5

-- Recommend to validate: 1, 3, 4

end TestCases
