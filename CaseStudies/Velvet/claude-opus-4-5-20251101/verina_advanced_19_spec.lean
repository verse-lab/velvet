import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isCleanPalindrome: Check if a string is a palindrome ignoring non-alphabetic characters and case
    Natural language breakdown:
    1. A palindrome is a string that reads the same forwards and backwards
    2. The function should ignore all non-alphabetic characters (whitespace, punctuation, etc.)
    3. The function should treat uppercase and lowercase letters as equivalent
    4. First, filter the string to keep only alphabetic characters
    5. Convert all remaining characters to lowercase for comparison
    6. Check if the cleaned string equals its reverse
    7. Return true if it's a palindrome, false otherwise
    8. Empty strings and single characters are trivially palindromes
    9. Examples:
       - "A man, a plan, a canal, Panama" -> clean to "amanaplanacanalpanama" -> palindrome (true)
       - "No lemon, no melon" -> clean to "nolonemonelon" -> palindrome (true)
       - "OpenAI" -> clean to "openai" -> not a palindrome (false)
-/

section Specs

-- Helper Functions

-- Filter to keep only alphabetic characters and convert to lowercase
def cleanString (s : String) : List Char :=
  (s.toList.filter Char.isAlpha).map Char.toLower

-- Check if a list is a palindrome (equals its reverse)
def isPalindrome (chars : List Char) : Prop :=
  chars = chars.reverse

-- Postcondition clauses
-- The result is true if and only if the cleaned string is a palindrome
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ cleanString s = (cleanString s).reverse

def precondition (s : String) :=
  True  -- no preconditions

def postcondition (s : String) (result : Bool) :=
  ensures1 s result

end Specs

section Impl

method isCleanPalindrome (s: String)
  return (result: Bool)
  require precondition s
  ensures postcondition s result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: Classic palindrome with spaces and punctuation (example from problem)
def test1_s : String := "A man, a plan, a canal, Panama"
def test1_Expected : Bool := true

-- Test case 2: Another classic palindrome phrase
def test2_s : String := "No lemon, no melon"
def test2_Expected : Bool := true

-- Test case 3: Non-palindrome word
def test3_s : String := "OpenAI"
def test3_Expected : Bool := false

-- Test case 4: Question form palindrome
def test4_s : String := "Was it a car or a cat I saw?"
def test4_Expected : Bool := true

-- Test case 5: Non-palindrome greeting
def test5_s : String := "Hello, World!"
def test5_Expected : Bool := false

-- Test case 6: Empty string (edge case - trivially a palindrome)
def test6_s : String := ""
def test6_Expected : Bool := true

-- Test case 7: Single character (edge case - trivially a palindrome)
def test7_s : String := "A"
def test7_Expected : Bool := true

-- Test case 8: Only non-alphabetic characters (edge case - empty after cleaning)
def test8_s : String := "12345!@#$%"
def test8_Expected : Bool := true

-- Test case 9: Simple palindrome word
def test9_s : String := "Racecar"
def test9_Expected : Bool := true

-- Test case 10: Two same characters
def test10_s : String := "aa"
def test10_Expected : Bool := true

-- Recommend to validate: 1, 3, 6

end TestCases

