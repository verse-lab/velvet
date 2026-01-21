import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    runLengthEncode: Perform run-length encoding on a string
    Natural language breakdown:
    1. Given a string s, scan from left to right and group consecutive identical characters
    2. Each group becomes a pair (Char, Nat) where Nat is the count of consecutive occurrences
    3. For example, "aaabbc" becomes [('a', 3), ('b', 2), ('c', 1)]
    4. Properties the result must satisfy:
       a. No pair has a zero run-length (all counts are positive)
       b. Consecutive pairs must have different characters (no adjacent duplicates in encoded form)
       c. Decoding the output returns the original string
    5. Edge cases:
       - Empty string returns empty list
       - Single character returns list with one pair
       - All same characters returns single pair with total count
       - All different characters returns list of pairs each with count 1
-/

section Specs

-- Helper function to decode a run-length encoded list back to a list of characters
def decode (encoded : List (Char × Nat)) : List Char :=
  encoded.flatMap (fun p => List.replicate p.2 p.1)

-- Check that all run lengths are positive (no zero counts)
def allPositiveCounts (encoded : List (Char × Nat)) : Prop :=
  ∀ p ∈ encoded, p.2 > 0

-- Check that no two consecutive pairs have the same character
def noConsecutiveSameChar (encoded : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i + 1 < encoded.length → (encoded[i]!).1 ≠ (encoded[i + 1]!).1

-- Postcondition clause 1: All counts are positive
def ensures1 (s : String) (result : List (Char × Nat)) :=
  allPositiveCounts result

-- Postcondition clause 2: No consecutive pairs have the same character
def ensures2 (s : String) (result : List (Char × Nat)) :=
  noConsecutiveSameChar result

-- Postcondition clause 3: Decoding returns the original string
def ensures3 (s : String) (result : List (Char × Nat)) :=
  decode result = s.toList

def precondition (s : String) :=
  True  -- no preconditions

def postcondition (s : String) (result : List (Char × Nat)) :=
  ensures1 s result ∧
  ensures2 s result ∧
  ensures3 s result

end Specs

section Impl

method runLengthEncode (s : String)
  return (result : List (Char × Nat))
  require precondition s
  ensures postcondition s result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Empty string
def test1_s : String := ""
def test1_Expected : List (Char × Nat) := []

-- Test case 2: Single repeated character
def test2_s : String := "aaa"
def test2_Expected : List (Char × Nat) := [('a', 3)]

-- Test case 3: Multiple groups with repeated character appearing again
def test3_s : String := "abbbcccaa"
def test3_Expected : List (Char × Nat) := [('a', 1), ('b', 3), ('c', 3), ('a', 2)]

-- Test case 4: All different characters
def test4_s : String := "xyz"
def test4_Expected : List (Char × Nat) := [('x', 1), ('y', 1), ('z', 1)]

-- Test case 5: Alternating repeated groups
def test5_s : String := "aabbaa"
def test5_Expected : List (Char × Nat) := [('a', 2), ('b', 2), ('a', 2)]

-- Test case 6: Single character
def test6_s : String := "x"
def test6_Expected : List (Char × Nat) := [('x', 1)]

-- Test case 7: Two different characters
def test7_s : String := "ab"
def test7_Expected : List (Char × Nat) := [('a', 1), ('b', 1)]

-- Test case 8: Long run of same character
def test8_s : String := "aaaaaaaa"
def test8_Expected : List (Char × Nat) := [('a', 8)]

-- Test case 9: Alternating single characters
def test9_s : String := "ababab"
def test9_Expected : List (Char × Nat) := [('a', 1), ('b', 1), ('a', 1), ('b', 1), ('a', 1), ('b', 1)]

-- Test case 10: Mix of runs and singles
def test10_s : String := "aabccc"
def test10_Expected : List (Char × Nat) := [('a', 2), ('b', 1), ('c', 3)]

-- Recommend to validate: 1, 3, 4

end TestCases
