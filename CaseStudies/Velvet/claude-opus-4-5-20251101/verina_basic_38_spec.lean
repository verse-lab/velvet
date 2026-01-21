import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    allCharactersSame: Check whether all characters in a string are identical
    Natural language breakdown:
    1. Given a string s, determine if every character in the string is the same
    2. An empty string is considered to have all characters identical (vacuously true)
    3. A single-character string is considered to have all characters identical
    4. For strings with 2+ characters, all characters must be equal to the first character
    5. Return true if all characters are identical, false otherwise
    6. The key property: if the string is non-empty, every character equals the first character
-/

-- Helper Functions

section Specs

-- Helper Functions

-- Check if all characters in a list are the same as the first character
def allSameAsFirst (chars : List Char) : Prop :=
  match chars with
  | [] => True
  | c :: _ => ∀ i : Nat, i < chars.length → chars[i]! = c

-- Postcondition clauses
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ allSameAsFirst s.toList

def precondition (s : String) :=
  True  -- no preconditions

def postcondition (s : String) (result : Bool) :=
  ensures1 s result

end Specs

section Impl

-- Method Definition

method allCharactersSame (s: String)
  return (result: Bool)
  require precondition s
  ensures postcondition s result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: All same characters "aaa" (from problem examples)
def test1_s : String := "aaa"
def test1_Expected : Bool := true

-- Test case 2: Different characters "aba" (from problem examples)
def test2_s : String := "aba"
def test2_Expected : Bool := false

-- Test case 3: Empty string (edge case)
def test3_s : String := ""
def test3_Expected : Bool := true

-- Test case 4: Single character (edge case)
def test4_s : String := "a"
def test4_Expected : Bool := true

-- Test case 5: All same characters "bbbb" (from problem examples)
def test5_s : String := "bbbb"
def test5_Expected : Bool := true

-- Test case 6: Different characters "bbab" (from problem examples)
def test6_s : String := "bbab"
def test6_Expected : Bool := false

-- Test case 7: Two same characters
def test7_s : String := "xx"
def test7_Expected : Bool := true

-- Test case 8: Two different characters
def test8_s : String := "xy"
def test8_Expected : Bool := false

-- Test case 9: Long string with all same characters
def test9_s : String := "zzzzzzzzz"
def test9_Expected : Bool := true

-- Test case 10: Different character at the end
def test10_s : String := "aaaab"
def test10_Expected : Bool := false

-- Recommend to validate: 1, 2, 3

end TestCases
