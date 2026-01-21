import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    palindromeIgnoreNonAlnum: Check if a string is a palindrome ignoring non-alphanumeric characters and case
    Natural language breakdown:
    1. Given a string s, we need to determine if it's a palindrome
    2. When checking for palindrome, we ignore all non-alphanumeric characters
    3. The comparison is case-insensitive (treat 'A' and 'a' as the same)
    4. A palindrome reads the same forwards and backwards
    5. First, filter the string to keep only alphanumeric characters (using Char.isAlphanum)
    6. Then convert all characters to lowercase (using Char.toLower)
    7. Finally, check if the resulting list equals its reverse
    8. Empty strings are considered palindromes (trivially true)
    9. Examples:
       - "A man, a plan, a canal: Panama" -> filter & lower -> "amanaplanacanalpanama" -> true
       - "race a car" -> filter & lower -> "raceacar" -> false
-/

section Specs

-- Helper Functions

-- Extract alphanumeric characters and convert to lowercase
def normalizedChars (s : String) : List Char :=
  (s.toList.filter Char.isAlphanum).map Char.toLower

-- Postcondition: the result is true if and only if the normalized character list is a palindrome
def postcondition_clause (s : String) (result : Bool) :=
  let normalized := normalizedChars s
  result = (normalized == normalized.reverse)

def precondition (s : String) :=
  True  -- no preconditions

def postcondition (s : String) (result : Bool) :=
  postcondition_clause s result

end Specs

section Impl

method palindromeIgnoreNonAlnum (s : String)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: Example from problem - famous palindrome phrase
def test1_s : String := "A man, a plan, a canal: Panama"
def test1_Expected : Bool := true

-- Test case 2: Empty string (trivially a palindrome)
def test2_s : String := ""
def test2_Expected : Bool := true

-- Test case 3: Non-palindrome with spaces
def test3_s : String := "race a car"
def test3_Expected : Bool := false

-- Test case 4: Palindrome with mixed case and punctuation
def test4_s : String := "No 'x' in Nixon"
def test4_Expected : Bool := true

-- Test case 5: Palindrome with special characters
def test5_s : String := "abc!!cba?"
def test5_Expected : Bool := true

-- Test case 6: Non-palindrome sentence
def test6_s : String := "Hello, world!"
def test6_Expected : Bool := false

-- Test case 7: Single character (trivially a palindrome)
def test7_s : String := "a"
def test7_Expected : Bool := true

-- Test case 8: Only non-alphanumeric characters (empty after filtering, so palindrome)
def test8_s : String := "!@#$%"
def test8_Expected : Bool := true

-- Test case 9: Simple palindrome without special characters
def test9_s : String := "racecar"
def test9_Expected : Bool := true

-- Test case 10: Two different characters
def test10_s : String := "ab"
def test10_Expected : Bool := false

-- Recommend to validate: 1, 3, 4

end TestCases
