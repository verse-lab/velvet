import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    toUppercase: Convert a string to uppercase
    Natural language breakdown:
    1. Given a string s, convert every lowercase letter to its uppercase equivalent
    2. All non-lowercase characters (uppercase letters, digits, punctuation, spaces) remain unchanged
    3. The output string must have the same length as the input string
    4. Character-by-character correspondence: for each position i, if input[i] is lowercase ('a'-'z'),
       output[i] is the corresponding uppercase letter ('A'-'Z'); otherwise output[i] = input[i]
    5. Lowercase ASCII letters are characters with code points 97-122 ('a' to 'z')
    6. Uppercase conversion subtracts 32 from the code point (e.g., 'a' (97) → 'A' (65))
    7. Empty string produces empty string
    8. Using Char.toUpper from Lean's standard library handles the character conversion
-/

section Specs

-- Helper Functions

-- Postcondition clauses

-- The result has the same length as the input
def ensures1 (s : String) (result : String) :=
  result.length = s.length

-- Each character in the result is the uppercase version of the corresponding input character
def ensures2 (s : String) (result : String) :=
  ∀ i : Nat, i < s.length → result.toList[i]! = (s.toList[i]!).toUpper

def precondition (s : String) :=
  True  -- no preconditions, any string is valid

def postcondition (s : String) (result : String) :=
  ensures1 s result ∧ ensures2 s result

end Specs

section Impl

method toUppercase (s: String)
  return (result: String)
  require precondition s
  ensures postcondition s result
  do
  pure ""  -- placeholder

end Impl

section TestCases

-- Test case 1: Mixed case string with punctuation (from problem example)
def test1_s : String := "Hello, World!"
def test1_Expected : String := "HELLO, WORLD!"

-- Test case 2: All lowercase letters
def test2_s : String := "abc"
def test2_Expected : String := "ABC"

-- Test case 3: All uppercase letters (no change expected)
def test3_s : String := "ABC"
def test3_Expected : String := "ABC"

-- Test case 4: Digits and special characters only (no change expected)
def test4_s : String := "123!?@"
def test4_Expected : String := "123!?@"

-- Test case 5: Empty string
def test5_s : String := ""
def test5_Expected : String := ""

-- Test case 6: Single lowercase character
def test6_s : String := "z"
def test6_Expected : String := "Z"

-- Test case 7: Single uppercase character (no change)
def test7_s : String := "A"
def test7_Expected : String := "A"

-- Test case 8: Mixed with numbers and spaces
def test8_s : String := "test 123 abc"
def test8_Expected : String := "TEST 123 ABC"

-- Test case 9: All same lowercase letter
def test9_s : String := "aaaa"
def test9_Expected : String := "AAAA"

-- Test case 10: Boundary characters (just before and after lowercase range)
def test10_s : String := "`{az"
def test10_Expected : String := "`{AZ"

-- Recommend to validate: 1, 2, 5

end TestCases
