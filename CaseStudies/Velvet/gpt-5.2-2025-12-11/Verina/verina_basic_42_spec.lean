import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    countDigits: Count the number of ASCII digit characters ('0'..'9') in a string.
    Natural language breakdown:
    1. Input is a string s.
    2. Consider the characters of s in order.
    3. A character is a digit iff Char.isDigit returns true (equivalently '0'..'9').
    4. The output is the number of characters in s that are digits.
    5. There are no preconditions; the function must work for any string.
-/

section Specs

-- Helper: digit predicate (use the standard library definition)
def isDigitChar (c : Char) : Bool :=
  c.isDigit

-- Helper: count digit characters in a string via List.countP over s.toList.
-- Note: This is a mathematical characterization of the intended result.
def digitCount (s : String) : Nat :=
  (s.toList.countP (fun c => isDigitChar c))

-- No preconditions

def precondition (s : String) : Prop :=
  True

-- Postcondition: result equals the number of digit characters in s.
-- This uniquely determines the output.
def postcondition (s : String) (result : Nat) : Prop :=
  result = digitCount s

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

-- Test case 1: mixed digits and letters (given example)
def test1_s : String := "123abc456"
def test1_Expected : Nat := 6

-- Test case 2: no digits
def test2_s : String := "no digits here!"
def test2_Expected : Nat := 0

-- Test case 3: all digits
def test3_s : String := "1234567890"
def test3_Expected : Nat := 10

-- Test case 4: empty string
def test4_s : String := ""
def test4_Expected : Nat := 0

-- Test case 5: alternating letters and digits
def test5_s : String := "a1b2c3"
def test5_Expected : Nat := 3

-- Test case 6: single digit zero
def test6_s : String := "0"
def test6_Expected : Nat := 1

-- Test case 7: only letters
def test7_s : String := "abc"
def test7_Expected : Nat := 0

-- Test case 8: punctuation and spaces with digits
def test8_s : String := " 9!x-0?"
def test8_Expected : Nat := 2

-- Test case 9: newline and tab around digits
def test9_s : String := "\n7\t"
def test9_Expected : Nat := 1

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 3, 8

end TestCases
