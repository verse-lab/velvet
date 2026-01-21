import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    reverseString: Reverse the characters of a given string
    Natural language breakdown:
    1. Given a string s (which may be empty), return a new string with characters in reverse order
    2. The result string should have the same length as the input string
    3. The character at position i in the result should equal the character at position (length - 1 - i) in the input
    4. An empty string reversed is an empty string
    5. A single character string reversed is itself
    6. A palindrome reversed equals itself
    7. Using Mathlib's List.reverse on the character list gives the reversed string
-/

section Specs

-- Precondition: no constraints on input string
def precondition (s : String) : Prop :=
  True

-- Postcondition: the result is the reversal of the input string
-- Specified via index-wise correspondence and length preservation
def postcondition (s : String) (result : String) : Prop :=
  let inputChars := s.toList
  let resultChars := result.toList
  -- Length is preserved
  resultChars.length = inputChars.length ∧
  -- Each character at position i in result equals character at position (length - 1 - i) in input
  (∀ i : Nat, i < inputChars.length →
    resultChars[i]! = inputChars[inputChars.length - 1 - i]!)

end Specs

section Impl

method reverseString (s: String)
  return (result: String)
  require precondition s
  ensures postcondition s result
  do
  pure ""

end Impl

section TestCases

-- Test case 1: Basic string reversal (from problem examples)
def test1_s : String := "hello"
def test1_Expected : String := "olleh"

-- Test case 2: Single character (from problem examples)
def test2_s : String := "a"
def test2_Expected : String := "a"

-- Test case 3: Empty string (from problem examples)
def test3_s : String := ""
def test3_Expected : String := ""

-- Test case 4: Palindrome (from problem examples)
def test4_s : String := "racecar"
def test4_Expected : String := "racecar"

-- Test case 5: Mixed case (from problem examples)
def test5_s : String := "Lean"
def test5_Expected : String := "naeL"

-- Test case 6: String with spaces
def test6_s : String := "hello world"
def test6_Expected : String := "dlrow olleh"

-- Test case 7: String with numbers
def test7_s : String := "abc123"
def test7_Expected : String := "321cba"

-- Test case 8: Two characters
def test8_s : String := "ab"
def test8_Expected : String := "ba"

-- Test case 9: Repeated characters
def test9_s : String := "aaa"
def test9_Expected : String := "aaa"

-- Test case 10: Special characters
def test10_s : String := "!@#"
def test10_Expected : String := "#@!"

-- Recommend to validate: 1, 2, 3

end TestCases
