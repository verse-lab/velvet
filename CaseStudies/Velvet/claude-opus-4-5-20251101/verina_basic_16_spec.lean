import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    replaceChars: Replace every occurrence of a specified character in a string with a new character
    Natural language breakdown:
    1. Given a string s, a character oldChar to find, and a character newChar to substitute
    2. Every occurrence of oldChar in s should be replaced with newChar
    3. All characters that are not oldChar remain unchanged
    4. The output string has the same length as the input string
    5. The transformation is position-preserving: character at position i in result corresponds to character at position i in input
    6. If oldChar does not appear in s, the result is identical to s
    7. If oldChar equals newChar, the result is identical to s
    8. Empty string input yields empty string output
-/

section Specs

-- Precondition: No restrictions on input
def precondition (s : String) (oldChar : Char) (newChar : Char) :=
  True

-- Postcondition: Specifies the character replacement properties
-- 1. Result has the same length as input
-- 2. For each position i:
--    - If input[i] = oldChar, then result[i] = newChar
--    - Otherwise, result[i] = input[i] (unchanged)
def postcondition (s : String) (oldChar : Char) (newChar : Char) (result : String) :=
  result.length = s.length ∧
  ∀ i : Nat, i < s.length →
    (s.toList[i]! = oldChar → result.toList[i]! = newChar) ∧
    (s.toList[i]! ≠ oldChar → result.toList[i]! = s.toList[i]!)

end Specs

section Impl

method replaceChars (s : String) (oldChar : Char) (newChar : Char)
  return (result : String)
  require precondition s oldChar newChar
  ensures postcondition s oldChar newChar result
  do
  pure ""

end Impl

section TestCases

-- Test case 1: Replace comma with semicolon (example from problem)
def test1_s : String := "hello, world!"
def test1_oldChar : Char := ','
def test1_newChar : Char := ';'
def test1_Expected : String := "hello; world!"

-- Test case 2: Replace comma with colon in mixed punctuation string
def test2_s : String := "a,b.c"
def test2_oldChar : Char := ','
def test2_newChar : Char := ':'
def test2_Expected : String := "a:b.c"

-- Test case 3: Replace lowercase 'o' with uppercase 'O' (multiple occurrences)
def test3_s : String := "hello, world!"
def test3_oldChar : Char := 'o'
def test3_newChar : Char := 'O'
def test3_Expected : String := "hellO, wOrld!"

-- Test case 4: Empty string (edge case)
def test4_s : String := ""
def test4_oldChar : Char := 'x'
def test4_newChar : Char := 'y'
def test4_Expected : String := ""

-- Test case 5: Character not present in string (no change)
def test5_s : String := "test"
def test5_oldChar : Char := 'x'
def test5_newChar : Char := 'y'
def test5_Expected : String := "test"

-- Test case 6: Replace character with itself (no change)
def test6_s : String := "unchanged"
def test6_oldChar : Char := 'u'
def test6_newChar : Char := 'u'
def test6_Expected : String := "unchanged"

-- Test case 7: All characters are the target (complete replacement)
def test7_s : String := "aaa"
def test7_oldChar : Char := 'a'
def test7_newChar : Char := 'b'
def test7_Expected : String := "bbb"

-- Test case 8: Single character string with match
def test8_s : String := "x"
def test8_oldChar : Char := 'x'
def test8_newChar : Char := 'y'
def test8_Expected : String := "y"

-- Test case 9: Single character string without match
def test9_s : String := "z"
def test9_oldChar : Char := 'x'
def test9_newChar : Char := 'y'
def test9_Expected : String := "z"

-- Recommend to validate: 1, 3, 7

end TestCases
