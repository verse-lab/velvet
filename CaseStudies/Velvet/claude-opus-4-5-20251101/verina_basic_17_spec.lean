import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    toLowercase: Convert all uppercase characters in a string to lowercase
    Natural language breakdown:
    1. Given a string s, convert every uppercase ASCII letter to its lowercase equivalent
    2. Characters that are not uppercase letters remain unchanged
    3. The output string must have the same length as the input string
    4. Each character at position i in the result corresponds to the lowercase conversion of character at position i in the input
    5. Uppercase ASCII letters are characters with code points 65-90 ('A'-'Z')
    6. Lowercase conversion adds 32 to the code point (e.g., 'A' (65) -> 'a' (97))
    7. Empty strings result in empty strings
    8. Strings with no uppercase letters remain unchanged
-/

section Specs

-- Precondition: no constraints on input string
def precondition (s : String) : Prop :=
  True

-- Postcondition: result has same length and each character is the lowercase version
def postcondition (s : String) (result : String) : Prop :=
  -- Length is preserved
  result.length = s.length ∧
  -- Each character is converted using Char.toLower
  (∀ i : Nat, i < s.length → result.data[i]! = s.data[i]!.toLower)

end Specs

section Impl

method toLowercase (s: String)
  return (result: String)
  require precondition s
  ensures postcondition s result
  do
  pure ""

end Impl

section TestCases

-- Test case 1: Mixed case with punctuation (from problem description)
def test1_s : String := "Hello, World!"
def test1_Expected : String := "hello, world!"

-- Test case 2: All uppercase
def test2_s : String := "ABC"
def test2_Expected : String := "abc"

-- Test case 3: All lowercase (should remain unchanged)
def test3_s : String := "abc"
def test3_Expected : String := "abc"

-- Test case 4: Empty string
def test4_s : String := ""
def test4_Expected : String := ""

-- Test case 5: Numbers and special characters (should remain unchanged)
def test5_s : String := "1234!@"
def test5_Expected : String := "1234!@"

-- Test case 6: Mixed alphanumeric
def test6_s : String := "MixedCASE123"
def test6_Expected : String := "mixedcase123"

-- Test case 7: Single uppercase character
def test7_s : String := "A"
def test7_Expected : String := "a"

-- Test case 8: Single lowercase character
def test8_s : String := "z"
def test8_Expected : String := "z"

-- Test case 9: Alternating case
def test9_s : String := "AbCdEf"
def test9_Expected : String := "abcdef"

-- Test case 10: All special characters
def test10_s : String := "!@#$%"
def test10_Expected : String := "!@#$%"

-- Recommend to validate: 1, 2, 4

end TestCases
