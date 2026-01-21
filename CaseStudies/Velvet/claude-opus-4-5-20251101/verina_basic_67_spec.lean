import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    IsPalindrome: Determine whether a given list of characters is a palindrome
    Natural language breakdown:
    1. A palindrome is a sequence that reads the same forward and backward
    2. The input is a list of characters (List Char)
    3. The function should return true if the list is a palindrome
    4. The function should return false if the list is not a palindrome
    5. An empty list is considered a palindrome (vacuously true)
    6. A single-element list is a palindrome
    7. A list is a palindrome if and only if it equals its reverse
    8. Using Mathlib's List.Palindrome definition: l.reverse = l
-/

section Specs

-- Helper Functions
-- Using Mathlib's List.reverse for reversing lists
-- Using the property: a list is a palindrome iff it equals its reverse

-- Postcondition clauses
-- The result is true if and only if the list equals its reverse
def ensures1 (x : List Char) (result : Bool) :=
  result = true ↔ x.reverse = x

def precondition (x : List Char) :=
  True  -- no preconditions, any list is valid input

def postcondition (x : List Char) (result : Bool) :=
  ensures1 x result

end Specs

section Impl

method IsPalindrome (x: List Char)
  return (result: Bool)
  require precondition x
  ensures postcondition x result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: Empty list (palindrome)
def test1_x : List Char := []
def test1_Expected : Bool := true

-- Test case 2: Single character (palindrome)
def test2_x : List Char := ['a']
def test2_Expected : Bool := true

-- Test case 3: Three characters forming palindrome "aba"
def test3_x : List Char := ['a', 'b', 'a']
def test3_Expected : Bool := true

-- Test case 4: Three characters not forming palindrome "abc"
def test4_x : List Char := ['a', 'b', 'c']
def test4_Expected : Bool := false

-- Test case 5: Seven character palindrome "racecar"
def test5_x : List Char := ['r', 'a', 'c', 'e', 'c', 'a', 'r']
def test5_Expected : Bool := true

-- Test case 6: Two same characters (palindrome)
def test6_x : List Char := ['x', 'x']
def test6_Expected : Bool := true

-- Test case 7: Two different characters (not palindrome)
def test7_x : List Char := ['a', 'b']
def test7_Expected : Bool := false

-- Test case 8: Even length palindrome "abba"
def test8_x : List Char := ['a', 'b', 'b', 'a']
def test8_Expected : Bool := true

-- Test case 9: Even length non-palindrome "abcd"
def test9_x : List Char := ['a', 'b', 'c', 'd']
def test9_Expected : Bool := false

-- Test case 10: All same characters (palindrome)
def test10_x : List Char := ['a', 'a', 'a', 'a']
def test10_Expected : Bool := true

-- Recommend to validate: 1, 3, 4

end TestCases
