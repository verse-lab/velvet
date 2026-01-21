import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    Match: Determine whether two strings match based on a wildcard pattern
    Natural language breakdown:
    1. Given two strings s and p of equal length
    2. For each position i, either s[i] equals p[i], or p[i] is the wildcard character '?'
    3. The wildcard '?' in p can match any character in s at that position
    4. Return true if all positions match according to the above rule
    5. Return false if any position fails to match (characters differ and p[i] is not '?')
    6. Precondition: both strings must have the same length
-/

section Specs

-- Precondition: both strings must have equal length
def precondition (s : String) (p : String) : Prop :=
  s.length = p.length

-- Postcondition: result is true iff for every position, either characters match or pattern has '?'
def postcondition (s : String) (p : String) (result : Bool) : Prop :=
  result = true ↔ (∀ i : Nat, i < s.length → (s.toList[i]! = p.toList[i]! ∨ p.toList[i]! = '?'))

end Specs

section Impl

method Match (s : String) (p : String)
  return (result : Bool)
  require precondition s p
  ensures postcondition s p result
  do
    pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic pattern with wildcard in middle (from problem description)
def test1_s : String := "abc"
def test1_p : String := "a?c"
def test1_Expected : Bool := true

-- Test case 2: Pattern with wildcard matching 'l'
def test2_s : String := "hello"
def test2_p : String := "he?lo"
def test2_Expected : Bool := true

-- Test case 3: Pattern with wildcard matching 'o'
def test3_s : String := "world"
def test3_p : String := "w?rld"
def test3_Expected : Bool := true

-- Test case 4: Pattern with wildcard matching 's'
def test4_s : String := "test"
def test4_p : String := "te?t"
def test4_Expected : Bool := true

-- Test case 5: No match - different characters without wildcard
def test5_s : String := "abc"
def test5_p : String := "abd"
def test5_Expected : Bool := false

-- Test case 6: All wildcards - should match any string of same length
def test6_s : String := "xyz"
def test6_p : String := "???"
def test6_Expected : Bool := true

-- Test case 7: Exact match - no wildcards needed
def test7_s : String := "same"
def test7_p : String := "same"
def test7_Expected : Bool := true

-- Test case 8: Empty strings - trivially match
def test8_s : String := ""
def test8_p : String := ""
def test8_Expected : Bool := true

-- Test case 9: Single character with wildcard
def test9_s : String := "x"
def test9_p : String := "?"
def test9_Expected : Bool := true

-- Test case 10: Multiple wildcards with some exact matches
def test10_s : String := "abcdef"
def test10_p : String := "a?c?e?"
def test10_Expected : Bool := true

-- Recommend to validate: 1, 5, 6

end TestCases
