import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    LongestCommonSubsequence: Find the length of the longest common subsequence of two arrays

    Natural language breakdown:
    1. We are given two arrays a and b of integers
    2. A subsequence of an array is a sequence that can be derived by deleting some or no elements
       without changing the order of the remaining elements
    3. A common subsequence of two arrays is a subsequence that appears in both arrays
    4. We need to find the length of the longest such common subsequence
    5. The result is a non-negative integer representing this length
    6. If one or both arrays are empty, the LCS length is 0
    7. If the arrays are identical, the LCS length equals the length of the arrays
    8. The LCS length is at most the minimum of the two array lengths
    9. We use List.Sublist from Lean which captures the subsequence relation
-/

section Specs

-- A common subsequence is a list that is a sublist of both input lists
def isCommonSubseq (s : List Int) (a : List Int) (b : List Int) : Prop :=
  List.Sublist s a ∧ List.Sublist s b

-- Postcondition clause 1: There exists a common subsequence with the given length
def ensures1 (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  ∃ s : List Int, isCommonSubseq s a.toList b.toList ∧ s.length = result.toNat

-- Postcondition clause 2: No common subsequence is longer than the result
def ensures2 (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  ∀ s : List Int, isCommonSubseq s a.toList b.toList → s.length ≤ result.toNat

-- Postcondition clause 3: Result is bounded by the minimum of array lengths
def ensures3 (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  result.toNat ≤ min a.size b.size

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True  -- No preconditions needed; works for any arrays including empty ones

def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  ensures1 a b result ∧
  ensures2 a b result ∧
  ensures3 a b result

end Specs

section Impl

method LongestCommonSubsequence (a : Array Int) (b : Array Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: Identical arrays
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[1, 2, 3]
def test1_Expected : Int := 3

-- Test case 2: One array is subsequence of other
def test2_a : Array Int := #[1, 3, 5, 7]
def test2_b : Array Int := #[1, 2, 3, 4, 5, 6, 7]
def test2_Expected : Int := 4

-- Test case 3: No common elements
def test3_a : Array Int := #[1, 2, 3]
def test3_b : Array Int := #[4, 5, 6]
def test3_Expected : Int := 0

-- Test case 4: First array empty
def test4_a : Array Int := #[]
def test4_b : Array Int := #[1, 2, 3]
def test4_Expected : Int := 0

-- Test case 5: Partial overlap
def test5_a : Array Int := #[1, 2, 3, 4]
def test5_b : Array Int := #[2, 4, 6, 8]
def test5_Expected : Int := 2

-- Test case 6: Second array empty
def test6_a : Array Int := #[1, 2, 3]
def test6_b : Array Int := #[]
def test6_Expected : Int := 0

-- Test case 7: Both arrays empty
def test7_a : Array Int := #[]
def test7_b : Array Int := #[]
def test7_Expected : Int := 0

-- Test case 8: Single element match
def test8_a : Array Int := #[5]
def test8_b : Array Int := #[5]
def test8_Expected : Int := 1

-- Test case 9: Single element no match
def test9_a : Array Int := #[5]
def test9_b : Array Int := #[3]
def test9_Expected : Int := 0

-- Test case 10: Classic LCS example with interleaving
def test10_a : Array Int := #[1, 0, 0, 1, 0, 1]
def test10_b : Array Int := #[0, 1, 0, 1, 1, 0]
def test10_Expected : Int := 4

-- Recommend to validate: 1, 2, 3

end TestCases
