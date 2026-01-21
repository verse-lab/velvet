import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    LongestCommonSubsequence: Find the length of the longest common subsequence of two input arrays.

    Natural language breakdown:
    1. A subsequence of a sequence is obtained by deleting some (possibly zero) elements
       without changing the order of remaining elements
    2. A common subsequence of two sequences is a sequence that is a subsequence of both
    3. The longest common subsequence (LCS) is the common subsequence with maximum length
    4. We need to return the length of the LCS, not the LCS itself
    5. If the arrays have no common elements, the LCS length is 0
    6. If one array is empty, the LCS length is 0
    7. If both arrays are identical, the LCS length equals the array length
    8. The LCS is not necessarily unique, but its length is unique
-/

section Specs
register_specdef_allow_recursion

-- A list s is a subsequence of list l if s can be obtained by deleting elements from l
-- We use List.Sublist from Mathlib which represents this concept
-- List.Sublist l₁ l₂ means l₁ is a sublist of l₂ (can delete elements from l₂ to get l₁)

-- Helper: check if a list is a common subsequence of two lists
def isCommonSubseq (s : List Int) (a : List Int) (b : List Int) : Prop :=
  s.Sublist a ∧ s.Sublist b

-- Helper: check if n is a valid LCS length for two lists
-- This means there exists a common subsequence of length n, and no common subsequence is longer
def isLCSLength (a : List Int) (b : List Int) (n : Nat) : Prop :=
  (∃ s : List Int, isCommonSubseq s a b ∧ s.length = n) ∧
  (∀ s : List Int, isCommonSubseq s a b → s.length ≤ n)

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True  -- No preconditions required

def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  isLCSLength a.toList b.toList result.toNat
end Specs

section Impl
method LongestCommonSubsequence (a : Array Int) (b : Array Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
    let m := a.size
    let n := b.size
    
    -- Handle empty array cases
    if m = 0 then
      return 0
    else
      if n = 0 then
        return 0
      else
        -- Create a 2D DP table using a flattened 1D array
        -- dp[i * (n+1) + j] represents LCS length of a[0..i-1] and b[0..j-1]
        let mut dp := Array.replicate ((m + 1) * (n + 1)) 0
        
        let mut i := 1
        while i <= m
          invariant true = true
          done_with i > m
        do
          let mut j := 1
          while j <= n
            invariant true = true
            done_with j > n
          do
            let aIdx := i - 1
            let bIdx := j - 1
            if a[aIdx]! = b[bIdx]! then
              -- Characters match: LCS extends by 1
              let prevVal := dp[(i - 1) * (n + 1) + (j - 1)]!
              dp := dp.set! (i * (n + 1) + j) (prevVal + 1)
            else
              -- Characters don't match: take max of excluding one character from either
              let topVal := dp[(i - 1) * (n + 1) + j]!
              let leftVal := dp[i * (n + 1) + (j - 1)]!
              if topVal >= leftVal then
                dp := dp.set! (i * (n + 1) + j) topVal
              else
                dp := dp.set! (i * (n + 1) + j) leftVal
            j := j + 1
          i := i + 1
        
        -- The result is in dp[m][n]
        let lcsLen := dp[m * (n + 1) + n]!
        return lcsLen
end Impl

section TestCases
-- Test case 1: Both arrays are identical [1, 2, 3]
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[1, 2, 3]
def test1_Expected : Int := 3

-- Test case 2: Subsequence is a subset of both arrays
def test2_a : Array Int := #[1, 3, 5, 7]
def test2_b : Array Int := #[1, 2, 3, 4, 5, 6, 7]
def test2_Expected : Int := 4

-- Test case 3: No common elements
def test3_a : Array Int := #[1, 2, 3]
def test3_b : Array Int := #[4, 5, 6]
def test3_Expected : Int := 0

-- Test case 4: First array is empty
def test4_a : Array Int := #[]
def test4_b : Array Int := #[1, 2, 3]
def test4_Expected : Int := 0

-- Test case 5: Partial overlap
def test5_a : Array Int := #[1, 2, 3, 4]
def test5_b : Array Int := #[2, 4, 6, 8]
def test5_Expected : Int := 2

-- Test case 6: Second array is empty
def test6_a : Array Int := #[1, 2, 3]
def test6_b : Array Int := #[]
def test6_Expected : Int := 0

-- Test case 7: Both arrays are empty
def test7_a : Array Int := #[]
def test7_b : Array Int := #[]
def test7_Expected : Int := 0

-- Test case 8: Single element arrays with same element
def test8_a : Array Int := #[5]
def test8_b : Array Int := #[5]
def test8_Expected : Int := 5

-- Test case 9: LCS is not contiguous in either array
def test9_a : Array Int := #[1, 0, 2, 0, 3]
def test9_b : Array Int := #[0, 1, 0, 2, 0, 3, 0]
def test9_Expected : Int := 5

-- Test case 10: Classic LCS example with interleaved elements
def test10_a : Array Int := #[1, 2, 3, 4, 1]
def test10_b : Array Int := #[3, 4, 1, 2, 1, 3]
def test10_Expected : Int := 3

-- Recommend to validate: 1, 2, 5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((LongestCommonSubsequence test1_a test1_b).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((LongestCommonSubsequence test2_a test2_b).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((LongestCommonSubsequence test3_a test3_b).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((LongestCommonSubsequence test4_a test4_b).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((LongestCommonSubsequence test5_a test5_b).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((LongestCommonSubsequence test6_a test6_b).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((LongestCommonSubsequence test7_a test7_b).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((LongestCommonSubsequence test8_a test8_b).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((LongestCommonSubsequence test9_a test9_b).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((LongestCommonSubsequence test10_a test10_b).run), DivM.res test10_Expected ]
end Assertions
