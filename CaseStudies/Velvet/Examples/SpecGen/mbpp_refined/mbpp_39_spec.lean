import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    RearrangeString: Check if letters of a string can be rearranged so that adjacent characters differ
    Natural language breakdown:
    1. Given a string of characters, determine if it's possible to rearrange them
    2. The rearrangement must satisfy: no two adjacent characters are identical
    3. If such a rearrangement exists, return it as a string
    4. If no valid rearrangement exists, the specification allows any string that cannot be valid
    5. Key insight: a valid rearrangement exists if and only if no character appears more than ⌈n/2⌉ times
       - For string of length n, the most frequent character can appear at most ⌈n/2⌉ times
       - This is because in the best case, we alternate the most frequent char with others
       - For n=3 and one char appearing 2 times: "aab" can become "aba" (valid)
       - For n=4 and one char appearing 3 times: "aaab" cannot be arranged (invalid)
    6. The result must be a permutation of the input (same characters, same counts)
    7. The result must have the property that result[i] ≠ result[i+1] for all valid i
    8. Empty strings and single characters are trivially valid
-/

-- Helper Functions

-- Check if a string is a permutation of another (same character counts)

section Specs

-- Helper Functions

def isPermutation (s1 s2: String) : Prop :=
  ∀ c, s1.toList.count c = s2.toList.count c

-- Check if no two adjacent characters are the same
def noAdjacentSame (s: String) : Prop :=
  let chars := s.toList
  ∀ i, i + 1 < chars.length → chars[i]! ≠ chars[i + 1]!

-- Count occurrences of a character in a string
def charCount (s: String) (c: Char) : Nat :=
  s.toList.count c

-- Find the maximum frequency of any character in the string
def maxCharFrequency (s: String) : Nat :=
  let chars := s.toList
  let uniqueChars := chars.eraseDups
  uniqueChars.foldl (fun max c => Nat.max max (charCount s c)) 0

-- Check if rearrangement is possible (greedy criterion)
def canRearrange (s: String) : Prop :=
  let n := s.length
  let maxFreq := maxCharFrequency s
  if n = 0 then True
  else maxFreq ≤ (n + 1) / 2

-- Postcondition clauses
def ensures1 (s : String) (result : String) :=
  isPermutation s result
def ensures2 (s : String) (result : String) :=
  canRearrange s → noAdjacentSame result
def ensures3 (s : String) (result : String) :=
  canRearrange s → (∀ r, (isPermutation s r ∧ noAdjacentSame r) → result ≤ r)
def ensures4 (s : String) (result : String) :=
  ¬canRearrange s → result = s

def precondition (s : String) :=
  True  -- no preconditions
def postcondition (s : String) (result : String) :=
  ensures1 s result ∧
  ensures2 s result ∧
  ensures3 s result ∧
  ensures4 s result

end Specs

section Impl

method RearrangeString (s: String)
  return (result: String)
  require precondition s
  ensures postcondition s result
  do
    sorry

prove_correct RearrangeString by sorry

end Impl

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
-- Input: "aab"
-- Character counts: 'a': 2, 'b': 1
-- Length: 3, maxFreq: 2, ceiling(3/2) = 2, so 2 ≤ 2 ✓ valid
-- Possible rearrangements: "aba", "baa" (only these two have no adjacent duplicates)
-- Lexicographically smallest: "aba" < "baa"
-- Verification:
--   - isPermutation "aab" "aba" ✓ (both have 2 'a's and 1 'b')
--   - noAdjacentSame "aba" ✓ ('a' ≠ 'b' and 'b' ≠ 'a')
def test1_s : String := "aab"
def test1_Expected : String := "aba"

-- Test case 2: Simple two-character string with duplicates
-- Input: "aa"
-- Character counts: 'a': 2
-- Length: 2, maxFreq: 2, ceiling(2/2) = 1, so 2 > 1 ✗ invalid
-- Cannot arrange two identical characters without adjacency
-- Any result will fail noAdjacentSame
def test2_s : String := "aa"
def test2_Expected : String := "aa"  -- No valid arrangement exists

-- Test case 3: Three different characters
-- Input: "abc"
-- Character counts: 'a': 1, 'b': 1, 'c': 1
-- Length: 3, maxFreq: 1, ceiling(3/2) = 2, so 1 ≤ 2 ✓ valid
-- Possible arrangements: "abc", "acb", "bac", "bca", "cab", "cba"
-- All are valid since all characters are distinct
-- Lexicographically smallest: "abc"
def test3_s : String := "abc"
def test3_Expected : String := "abc"

-- Test case 4: Longer string with valid arrangement
-- Input: "aaab"
-- Character counts: 'a': 3, 'b': 1
-- Length: 4, maxFreq: 3, ceiling(4/2) = 2, so 3 > 2 ✗ invalid
-- Cannot arrange: need to place 3 'a's in 4 positions with no adjacency
def test4_s : String := "aaab"
def test4_Expected : String := "aaab"  -- No valid arrangement exists

-- Test case 5: Perfectly alternating case
-- Input: "aabb"
-- Character counts: 'a': 2, 'b': 2
-- Length: 4, maxFreq: 2, ceiling(4/2) = 2, so 2 ≤ 2 ✓ valid
-- Possible arrangements: "abab", "baba"
-- Lexicographically smallest: "abab" < "baba"
def test5_s : String := "aabb"
def test5_Expected : String := "abab"

-- Test case 6: Empty string (edge case)
-- Input: ""
-- Length: 0, trivially valid
-- Result must also be empty
def test6_s : String := ""
def test6_Expected : String := ""

-- Test case 7: Single character (edge case)
-- Input: "a"
-- Length: 1, maxFreq: 1, ceiling(1/2) = 1, so 1 ≤ 1 ✓ valid
-- Single character has no adjacent pairs, trivially valid
def test7_s : String := "a"
def test7_Expected : String := "a"

-- Test case 8: Complex valid case
-- Input: "aaabbc"
-- Character counts: 'a': 3, 'b': 2, 'c': 1
-- Length: 6, maxFreq: 3, ceiling(6/2) = 3, so 3 ≤ 3 ✓ valid
-- Possible arrangements: "ababac", "abacab", "bacaba", "cababa", etc.
-- Lexicographically smallest: "ababac"
def test8_s : String := "aaabbc"
def test8_Expected : String := "ababac"

-- Test case 9: All same character (invalid for length > 1)
-- Input: "aaaa"
-- Character counts: 'a': 4
-- Length: 4, maxFreq: 4, ceiling(4/2) = 2, so 4 > 2 ✗ invalid
def test9_s : String := "aaaa"
def test9_Expected : String := "aaaa"  -- No valid arrangement exists

-- Test case 10: Large valid case
-- Input: "aabbccdd"
-- Character counts: all chars appear exactly 2 times
-- Length: 8, maxFreq: 2, ceiling(8/2) = 4, so 2 ≤ 4 ✓ valid
-- Possible arrangements: "ababcdcd", "abacbdcd", "abcdabcd", etc.
-- Lexicographically smallest: "ababcdcd"
def test10_s : String := "aabbccdd"
def test10_Expected : String := "ababcdcd"

-- Test case 11: Boundary case where maxFreq exactly equals ceiling(n/2)
-- Input: "aaabbb"
-- Character counts: 'a': 3, 'b': 3
-- Length: 6, maxFreq: 3, ceiling(6/2) = 3, so 3 ≤ 3 ✓ valid
-- Possible arrangements: "ababab", "bababa"
-- Lexicographically smallest: "ababab" < "bababa"
def test11_s : String := "aaabbb"
def test11_Expected : String := "ababab"

-- Test case 12: Long string with valid distribution
-- Input: "programming"
-- Character counts: 'p': 1, 'r': 2, 'o': 1, 'g': 2, 'a': 1, 'm': 2, 'i': 1, 'n': 1
-- Length: 11, maxFreq: 2, ceiling(11/2) = 6, so 2 ≤ 6 ✓ valid
-- Many valid arrangements possible
-- Lexicographically smallest: "agigmnmorpr"
def test12_s : String := "programming"
def test12_Expected : String := "agigmnmorpr"  -- Lexicographically smallest valid rearrangement

-- Recommend to validate: test cases 1, 3, 5, 6, 8, 11
-- These cover:
-- - Test 1: Problem statement example (required)
-- - Test 3: All distinct characters (trivial valid case)
-- - Test 5: Perfectly balanced two-character case
-- - Test 6: Empty string edge case
-- - Test 8: Complex valid case with three different characters
-- - Test 11: Boundary case where maxFreq = ceiling(n/2)

end TestCases
