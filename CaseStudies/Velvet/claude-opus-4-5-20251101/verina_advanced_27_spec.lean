import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    longestCommonSubsequence: Compute the longest common subsequence of two input strings
    Natural language breakdown:
    1. A subsequence of a string is derived by deleting zero or more characters without changing order
    2. A common subsequence of two strings is a subsequence of both strings
    3. The longest common subsequence (LCS) is a common subsequence with maximum length
    4. If multiple LCS exist with the same length, any one of them is acceptable
    5. The result must be a subsequence of the first input string s1
    6. The result must be a subsequence of the second input string s2
    7. No common subsequence can be longer than the result
    8. Empty strings have empty LCS with any other string
    9. If strings share no characters, the LCS is empty
-/

section Specs

-- Helper Functions

-- Check if a string is a subsequence of another string using Mathlib's List.Sublist
def isStringSubseq (sub : String) (s : String) : Prop :=
  sub.toList.Sublist s.toList

-- A string is a common subsequence of two strings if it's a subsequence of both
def isCommonSubseq (sub : String) (s1 : String) (s2 : String) : Prop :=
  isStringSubseq sub s1 ∧ isStringSubseq sub s2

-- Postcondition clauses
-- The result is a subsequence of s1
def ensures1 (s1 : String) (s2 : String) (result : String) :=
  isStringSubseq result s1

-- The result is a subsequence of s2
def ensures2 (s1 : String) (s2 : String) (result : String) :=
  isStringSubseq result s2

-- The result has maximum length among all common subsequences
def ensures3 (s1 : String) (s2 : String) (result : String) :=
  ∀ other : String, isCommonSubseq other s1 s2 → other.length ≤ result.length

def precondition (s1 : String) (s2 : String) :=
  True  -- no preconditions

def postcondition (s1 : String) (s2 : String) (result : String) :=
  ensures1 s1 s2 result ∧
  ensures2 s1 s2 result ∧
  ensures3 s1 s2 result

end Specs

section Impl

method longestCommonSubsequence (s1: String) (s2: String)
  return (result: String)
  require precondition s1 s2
  ensures postcondition s1 s2 result
  do
    pure ""

end Impl

section TestCases

-- Test case 1: Example from problem - "abcde" and "ace" -> "ace"
def test1_s1 : String := "abcde"
def test1_s2 : String := "ace"
def test1_Expected : String := "ace"

-- Test case 2: Repeated characters - "aaaa" and "bbaaa" -> "aaa"
def test2_s1 : String := "aaaa"
def test2_s2 : String := "bbaaa"
def test2_Expected : String := "aaa"

-- Test case 3: No common characters - "xyz" and "abc" -> ""
def test3_s1 : String := "xyz"
def test3_s2 : String := "abc"
def test3_Expected : String := ""

-- Test case 4: LCS is almost entire string - "axbxc" and "abxc" -> "abxc"
def test4_s1 : String := "axbxc"
def test4_s2 : String := "abxc"
def test4_Expected : String := "abxc"

-- Test case 5: Mixed case letters - "AGGTAB" and "GXTXAYB" -> "GTAB"
def test5_s1 : String := "AGGTAB"
def test5_s2 : String := "GXTXAYB"
def test5_Expected : String := "GTAB"

-- Test case 6: Empty first string
def test6_s1 : String := ""
def test6_s2 : String := "abc"
def test6_Expected : String := ""

-- Test case 7: Empty second string
def test7_s1 : String := "abc"
def test7_s2 : String := ""
def test7_Expected : String := ""

-- Test case 8: Both strings empty
def test8_s1 : String := ""
def test8_s2 : String := ""
def test8_Expected : String := ""

-- Test case 9: Identical strings
def test9_s1 : String := "hello"
def test9_s2 : String := "hello"
def test9_Expected : String := "hello"

-- Test case 10: One string is subsequence of other
def test10_s1 : String := "abc"
def test10_s2 : String := "aXbYcZ"
def test10_Expected : String := "abc"

-- Recommend to validate: 1, 3, 4

end TestCases
