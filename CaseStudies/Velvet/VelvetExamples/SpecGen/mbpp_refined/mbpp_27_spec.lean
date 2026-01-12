import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 27: Remove all digits from a list of strings
--
-- Natural language breakdown:
-- 1. We have a list of strings as input
-- 2. Each string may contain various characters including digits (0-9), letters, punctuation, etc.
-- 3. A digit is any character in the range '0' to '9'
-- 4. For each string in the input list, we need to remove all digit characters
-- 5. The result is a list of strings with the same length as the input list
-- 6. Each result string preserves all non-digit characters from the corresponding input string
-- 7. The order of strings in the list is preserved
-- 8. Within each string, the relative order of non-digit characters is preserved
-- 9. If a string contains only digits, the result should be an empty string
-- 10. If a string contains no digits, it remains unchanged
--
-- Property-oriented specification approach:
-- Instead of describing the algorithm (iterate through strings, filter characters),
-- we specify what properties the output must satisfy:
-- - The result list has the same length as the input list
-- - Each result string contains no digits
-- - Each result string is formed by removing only digits from the corresponding input string
-- - The order of non-digit characters in each string is preserved
-- - No characters are added, only removed

-- Helper function to check if a character is a digit

section Specs

-- Helper Functions

def isDigit (c : Char) : Bool := c.isDigit

-- Helper function to remove all digits from a single string
def isRemoveDigits (s : String) (t : String) :=
  t = String.mk (s.data.filter (fun c => !isDigit c))

-- Postcondition clauses
def ensures1 (strings : List String) (result : List String) :=
  result.length = strings.length ∧
  ∀ i, i < strings.length → isRemoveDigits strings[i]! result[i]!

def precondition (strings : List String) :=
  True  -- no preconditions
def postcondition (strings : List String) (result : List String) :=
  ensures1 strings result

end Specs

method RemoveDigitsFromList (strings: List String)
  return (result: List String)
  require precondition strings
  ensures postcondition strings result
  do
    sorry

prove_correct RemoveDigitsFromList by sorry

-- Test cases for specification validation
section TestCases
-- Test case 0: From problem description
def test0_arr : List String := ["4words", "3letters", "4digits"]
def test0_Expected : List String := ["words", "letters", "digits"]

-- Test case 1: Strings with no digits
def test1_arr : List String := ["hello", "world", "test"]
def test1_Expected : List String := ["hello", "world", "test"]

-- Test case 2: Strings with only digits
def test2_arr : List String := ["123", "456", "789"]
def test2_Expected : List String := ["", "", ""]

-- Test case 3: Mixed content with digits scattered throughout
def test3_arr : List String := ["a1b2c3", "x9y8z7", "m5n6"]
def test3_Expected : List String := ["abc", "xyz", "mn"]

-- Test case 4: Empty list
def test4_arr : List String := []
def test4_Expected : List String := []

-- Test case 5: List with empty strings
def test5_arr : List String := ["", "", "test"]
def test5_Expected : List String := ["", "", "test"]

-- Test case 6: Strings with digits at different positions
def test6_arr : List String := ["123abc", "abc123", "a1b2c3"]
def test6_Expected : List String := ["abc", "abc", "abc"]

-- Test case 7: Strings with special characters and digits
def test7_arr : List String := ["hello123!", "test@456#", "code789$"]
def test7_Expected : List String := ["hello!", "test@#", "code$"]

-- Test case 8: Single string in list
def test8_arr : List String := ["a1b2c3d4e5"]
def test8_Expected : List String := ["abcde"]

-- Test case 9: Strings with consecutive digits
def test9_arr : List String := ["test000", "aaa111bbb", "xyz999xyz"]
def test9_Expected : List String := ["test", "aaabbb", "xyzxyz"]

-- Test case 10: Large-scale input with many strings
def test10_arr : List String := [
  "abc123", "def456", "ghi789", "jkl012", "mno345",
  "pqr678", "stu901", "vwx234", "yza567", "bcd890",
  "efg123", "hij456", "klm789", "nop012", "qrs345",
  "tuv678", "wxy901", "zab234", "cde567", "fgh890"
]
def test10_Expected : List String := [
  "abc", "def", "ghi", "jkl", "mno",
  "pqr", "stu", "vwx", "yza", "bcd",
  "efg", "hij", "klm", "nop", "qrs",
  "tuv", "wxy", "zab", "cde", "fgh"
]

-- Test case 11: Strings with all digit characters 0-9
def test11_arr : List String := ["0a1b2c3d4e5f6g7h8i9j"]
def test11_Expected : List String := ["abcdefghij"]

-- Test case 12: Strings with uppercase, lowercase, and digits
def test12_arr : List String := ["Test123", "DATA456", "CoDe789"]
def test12_Expected : List String := ["Test", "DATA", "CoDe"]

-- Test case 13: Large string with many digits
def test13_arr : List String := [
  "The1quick2brown3fox4jumps5over6the7lazy8dog9and0runs1fast2very3much4indeed5"
]
def test13_Expected : List String := [
  "Thequickbrownfoxjumpsoverthelazydogandrunsfastverymuchiideed"
]

-- Test case 14: Strings with only one digit each
def test14_arr : List String := ["a1", "b2", "c3", "d4", "e5"]
def test14_Expected : List String := ["a", "b", "c", "d", "e"]

-- Recommend to validate: 0, 2, 3, 4, 7, 10

-- Verification summary:
-- All test cases verify the key properties:
-- 1. Length preservation (result list has same length as input)
-- 2. Digit removal (no digits in result strings)
-- 3. Character preservation (non-digit characters preserved in order)
-- 4. Edge cases: empty list, empty strings, strings with only digits
-- 5. Various patterns: digits at start/middle/end, consecutive digits
-- 6. Special characters and punctuation are preserved
-- 7. Case sensitivity is preserved
-- 8. Large-scale inputs for performance testing

end TestCases
