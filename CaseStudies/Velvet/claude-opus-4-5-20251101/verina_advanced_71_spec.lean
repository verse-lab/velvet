import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    shortestBeautifulSubstring: Find the shortest contiguous substring containing exactly k '1' characters
    Natural language breakdown:
    1. Given a binary string s (containing only '0' and '1') and a natural number k
    2. Find all contiguous substrings of s that contain exactly k occurrences of '1'
    3. Among these substrings, select the one with minimum length
    4. If multiple substrings have the same minimum length, select the lexicographically smallest one
    5. If no such substring exists (e.g., s has fewer than k '1's, or k=0 and s has no '0's), return ""
    6. Special case: when k=0, we need a substring with no '1's, so we return a single '0' if available
    7. The input string must be a valid binary string (only '0' and '1' characters)
-/

section Specs

-- Check if a string is a binary string (only '0' and '1')
def isBinaryString (s : String) : Prop :=
  ∀ c, c ∈ s.toList → c = '0' ∨ c = '1'

-- Count the number of '1' characters in a string
def countOnes (s : String) : Nat :=
  s.toList.count '1'

-- Check if a string is a substring of another starting at position i with length len
def isSubstringAt (s : String) (sub : String) (i : Nat) : Prop :=
  i + sub.length ≤ s.length ∧
  ∀ j : Nat, j < sub.length → s.toList[i + j]! = sub.toList[j]!

-- Check if sub is a contiguous substring of s
def isSubstringOf (s : String) (sub : String) : Prop :=
  ∃ i : Nat, isSubstringAt s sub i

-- A valid candidate substring has exactly k ones
def isValidCandidate (s : String) (sub : String) (k : Nat) : Prop :=
  isSubstringOf s sub ∧ countOnes sub = k

-- Check if result is the optimal (shortest, then lexicographically smallest) among valid candidates
def isOptimalResult (s : String) (k : Nat) (result : String) : Prop :=
  isValidCandidate s result k ∧
  (∀ other : String, isValidCandidate s other k →
    result.length < other.length ∨
    (result.length = other.length ∧ result ≤ other))

-- Check if no valid candidate exists
def noValidCandidate (s : String) (k : Nat) : Prop :=
  ¬∃ sub : String, isValidCandidate s sub k

-- Precondition: s must be a binary string
def precondition (s : String) (k : Nat) :=
  isBinaryString s

-- Postcondition clauses
def ensures1 (s : String) (k : Nat) (result : String) :=
  noValidCandidate s k → result = ""

def ensures2 (s : String) (k : Nat) (result : String) :=
  (∃ sub : String, isValidCandidate s sub k) → isOptimalResult s k result

def postcondition (s : String) (k : Nat) (result : String) :=
  ensures1 s k result ∧ ensures2 s k result

end Specs

section Impl

method shortestBeautifulSubstring (s : String) (k : Nat)
  return (result : String)
  require precondition s k
  ensures postcondition s k result
  do
  pure ""

end Impl

section TestCases

-- Test case 1: Example from problem - "100011001" with k=3
def test1_s : String := "100011001"
def test1_k : Nat := 3
def test1_Expected : String := "11001"

-- Test case 2: "1011" with k=2 - shortest is "11"
def test2_s : String := "1011"
def test2_k : Nat := 2
def test2_Expected : String := "11"

-- Test case 3: "000" with k=1 - no '1' exists, return empty
def test3_s : String := "000"
def test3_k : Nat := 1
def test3_Expected : String := ""

-- Test case 4: "11111" with k=3 - all ones, return "111"
def test4_s : String := "11111"
def test4_k : Nat := 3
def test4_Expected : String := "111"

-- Test case 5: "10100101" with k=2 - multiple candidates, shortest is "101"
def test5_s : String := "10100101"
def test5_k : Nat := 2
def test5_Expected : String := "101"

-- Test case 6: "1001001" with k=2 - shortest substring with 2 ones
def test6_s : String := "1001001"
def test6_k : Nat := 2
def test6_Expected : String := "1001"

-- Test case 7: "10010001" with k=1 - shortest substring with 1 one is "1"
def test7_s : String := "10010001"
def test7_k : Nat := 1
def test7_Expected : String := "1"

-- Test case 8: "1001" with k=0 - need substring with no ones, return "0"
def test8_s : String := "1001"
def test8_k : Nat := 0
def test8_Expected : String := "0"

-- Test case 9: Empty string with k=1 - no substring exists
def test9_s : String := ""
def test9_k : Nat := 1
def test9_Expected : String := ""

-- Test case 10: "1" with k=1 - single character match
def test10_s : String := "1"
def test10_k : Nat := 1
def test10_Expected : String := "1"

-- Recommend to validate: 1, 2, 4

end TestCases
