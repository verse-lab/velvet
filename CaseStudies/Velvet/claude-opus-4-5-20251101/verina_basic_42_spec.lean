import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- countDigits: Count the number of digit characters in a given string
--
-- Natural language breakdown:
-- 1. A digit character is any character between '0' and '9' (ASCII values 48-57)
-- 2. The method should count how many such digit characters appear in the input string
-- 3. The input is a string which can be empty or contain any characters
-- 4. The output is a non-negative natural number representing the count of digits
-- 5. There are no preconditions - the method works for any string
--
-- Key observations:
-- - Char.isDigit from Mathlib/Init provides the predicate for digit characters
-- - String.toList converts the string to a list of characters
-- - List.countP counts elements satisfying a predicate
-- - The result equals the number of characters c in s.toList where c.isDigit is true

section Specs

-- Precondition: no constraints on input
def precondition (s : String) :=
  True

-- Postcondition: result equals the count of digit characters in the string
-- Using List.countP with Char.isDigit predicate
def postcondition (s : String) (result : Nat) :=
  result = s.toList.countP (fun c => c.isDigit)

end Specs

section Impl

method countDigits (s: String)
  return (result: Nat)
  require precondition s
  ensures postcondition s result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Mixed alphanumeric string (from problem description)
def test1_s : String := "123abc456"
def test1_Expected : Nat := 6

-- Test case 2: String with no digits
def test2_s : String := "no digits here!"
def test2_Expected : Nat := 0

-- Test case 3: String with only digits
def test3_s : String := "1234567890"
def test3_Expected : Nat := 10

-- Test case 4: Empty string (edge case)
def test4_s : String := ""
def test4_Expected : Nat := 0

-- Test case 5: Alternating letters and digits
def test5_s : String := "a1b2c3"
def test5_Expected : Nat := 3

-- Test case 6: Single digit (minimal non-empty case)
def test6_s : String := "0"
def test6_Expected : Nat := 1

-- Test case 7: String with only letters (no digits)
def test7_s : String := "abc"
def test7_Expected : Nat := 0

-- Test case 8: Digits at boundaries
def test8_s : String := "1abc9"
def test8_Expected : Nat := 2

-- Test case 9: Special characters mixed with digits
def test9_s : String := "!@#1$%^2&*()3"
def test9_Expected : Nat := 3

-- Test case 10: Repeated same digit
def test10_s : String := "5555"
def test10_Expected : Nat := 4

-- Recommend to validate: 1, 4, 5

end TestCases
