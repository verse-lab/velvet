import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isPalindrome: Check if a given string is a palindrome
    Natural language breakdown:
    1. A palindrome is a string that reads the same forward and backward
    2. The input is a string s
    3. The output is a boolean indicating whether s is a palindrome
    4. To check if a string is a palindrome, we compare the list of characters with its reverse
    5. An empty string is considered a palindrome (trivially true)
    6. A single character string is always a palindrome
    7. Examples:
       - "racecar" reversed is "racecar" -> true
       - "abba" reversed is "abba" -> true
       - "abc" reversed is "cba" -> false
       - "" reversed is "" -> true
       - "a" reversed is "a" -> true
-/

section Specs

-- Helper Functions
-- Using Mathlib's List.reverse and String.toList

-- A string is a palindrome if its character list equals its reverse
def isPalindromeProperty (s : String) : Prop :=
  s.toList = s.toList.reverse

-- Postcondition: result is true iff the string is a palindrome
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ isPalindromeProperty s

def precondition (s : String) :=
  True  -- no preconditions

def postcondition (s : String) (result : Bool) :=
  ensures1 s result

end Specs

section Impl

method isPalindrome (s : String)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: "racecar" is a palindrome (odd length, classic example)
def test1_s : String := "racecar"
def test1_Expected : Bool := true

-- Test case 2: "abba" is a palindrome (even length)
def test2_s : String := "abba"
def test2_Expected : Bool := true

-- Test case 3: "abc" is not a palindrome
def test3_s : String := "abc"
def test3_Expected : Bool := false

-- Test case 4: empty string is a palindrome
def test4_s : String := ""
def test4_Expected : Bool := true

-- Test case 5: single character is a palindrome
def test5_s : String := "a"
def test5_Expected : Bool := true

-- Test case 6: two different characters is not a palindrome
def test6_s : String := "ab"
def test6_Expected : Bool := false

-- Test case 7: two same characters is a palindrome
def test7_s : String := "aa"
def test7_Expected : Bool := true

-- Test case 8: longer non-palindrome
def test8_s : String := "hello"
def test8_Expected : Bool := false

-- Test case 9: palindrome with spaces (treated as regular characters)
def test9_s : String := "a a"
def test9_Expected : Bool := true

-- Test case 10: case-sensitive check - "Aba" is not a palindrome (A != a)
def test10_s : String := "Aba"
def test10_Expected : Bool := false

-- Recommend to validate: 1, 3, 4

end TestCases
