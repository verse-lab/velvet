import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    MatchWordAtBeginning: Check if a string starts with a word (alphabetic characters)
    Natural language breakdown:
    1. A "word" is defined as a sequence of one or more alphabetic characters (letters)
    2. The function examines the beginning of the input string
    3. If the string starts with at least one alphabetic character, it should return "Matched!"
    4. If the string is empty, starts with whitespace, or starts with any non-alphabetic character, return "Not matched!"
    5. Only the very first character matters for determining if there's a match
    6. A match occurs if and only if the first character is alphabetic (isAlpha)
    7. The function returns one of two possible strings: "Matched!" or "Not matched!"
    8. Examples:
       - "python" starts with 'p' (alphabetic) -> "Matched!"
       - " python" starts with ' ' (space, not alphabetic) -> "Not matched!"
       - "" (empty string) has no first character -> "Not matched!"
       - "123abc" starts with '1' (digit, not alphabetic) -> "Not matched!"
-/

-- Helper Functions

section Specs

-- Helper Functions

def startsWithWord (s: String) : Bool :=
  match s.data with
  | [] => false
  | c :: _ => c.isAlpha

def expectedResult (s: String) : String :=
  if startsWithWord s then "Matched!" else "Not matched!"

-- Postcondition clauses
def ensures1 (input : String) (result : String) :=
  result = "Matched!" ∨ result = "Not matched!"
def ensures2 (input : String) (result : String) :=
  result = "Matched!" ↔ startsWithWord input

def precondition (input : String) :=
  True  -- no preconditions
def postcondition (input : String) (result : String) :=
  ensures1 input result ∧
  ensures2 input result

end Specs

method MatchWordAtBeginning (input: String)
  return (result: String)
  require precondition input
  ensures postcondition input result
  do
    sorry

prove_correct MatchWordAtBeginning by sorry

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
-- Input starts with space (not alphabetic)
def test1_input : String := " python"
def test1_Expected : String := "Not matched!"

-- Test case 2: String starts with alphabetic character
def test2_input : String := "python"
def test2_Expected : String := "Matched!"

-- Test case 3: Empty string
def test3_input : String := ""
def test3_Expected : String := "Not matched!"

-- Test case 4: String starts with digit
def test4_input : String := "123abc"
def test4_Expected : String := "Not matched!"

-- Test case 5: String starts with punctuation
def test5_input : String := "!hello"
def test5_Expected : String := "Not matched!"

-- Test case 6: Single alphabetic character
def test6_input : String := "a"
def test6_Expected : String := "Matched!"

-- Test case 7: Single non-alphabetic character
def test7_input : String := "1"
def test7_Expected : String := "Not matched!"

-- Test case 8: String starts with uppercase letter
def test8_input : String := "Python"
def test8_Expected : String := "Matched!"

-- Test case 9: String starts with tab character
def test9_input : String := "\tcode"
def test9_Expected : String := "Not matched!"

-- Test case 10: String starts with newline
def test10_input : String := "\nstart"
def test10_Expected : String := "Not matched!"

-- Test case 11: String with only alphabetic characters
def test11_input : String := "hello"
def test11_Expected : String := "Matched!"

-- Test case 12: String starts with special character
def test12_input : String := "@username"
def test12_Expected : String := "Not matched!"

-- Test case 13: String starts with underscore (not alphabetic in standard definition)
def test13_input : String := "_variable"
def test13_Expected : String := "Not matched!"

-- Test case 14: Long string starting with letter
def test14_input : String := "thequickbrownfoxjumpsoverthelazydog"
def test14_Expected : String := "Matched!"

-- Test case 15: Long string starting with non-letter
def test15_input : String := "   leading spaces before text"
def test15_Expected : String := "Not matched!"

-- Recommend to validate: test cases 1, 2, 3, 4, 5, 6
-- These cover:
-- - Test 1: Problem statement example (required) - starts with space
-- - Test 2: Normal word at beginning
-- - Test 3: Empty string edge case
-- - Test 4: Starts with digit
-- - Test 5: Starts with punctuation
-- - Test 6: Single character match

end TestCases
