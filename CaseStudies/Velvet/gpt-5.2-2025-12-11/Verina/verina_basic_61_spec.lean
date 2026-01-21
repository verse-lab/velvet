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
    allDigits: determine whether every character in a provided string is a digit.
    Natural language breakdown:
    1. Input is a well-formed string `s`.
    2. A character counts as a digit exactly when `Char.isDigit` is true for it (ASCII digits '0'..'9').
    3. The function returns `true` exactly when every character in `s` is a digit.
    4. If `s` is empty, the result is `true` (vacuously, all characters are digits).
    5. If at least one character in `s` is not a digit, the result is `false`.
-/

section Specs

-- Helper: decidable, Bool-based "all characters satisfy Char.isDigit" aggregator
-- Using `List.all` avoids non-decidable quantification over `Char`.
def allDigitsBool (s : String) : Bool :=
  s.toList.all Char.isDigit

-- No preconditions

def precondition (s : String) : Prop :=
  True

-- Postcondition: result is true iff `Char.isDigit` holds for every character in the string.
-- This formulation is computable and unambiguous.
def postcondition (s : String) (result : Bool) : Prop :=
  result = allDigitsBool s

end Specs

section Impl

method allDigits (s : String)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  pure false  -- placeholder

end Impl

section TestCases

-- Test case 1: example from prompt
-- "123456" -> true

def test1_s : String := "123456"
def test1_Expected : Bool := true

-- Test case 2: contains a non-digit letter
-- "123a56" -> false

def test2_s : String := "123a56"
def test2_Expected : Bool := false

-- Test case 3: empty string is vacuously all digits
-- "" -> true

def test3_s : String := ""
def test3_Expected : Bool := true

-- Test case 4: leading zeros are still digits
-- "007" -> true

def test4_s : String := "007"
def test4_Expected : Bool := true

-- Test case 5: contains whitespace
-- "98 76" -> false

def test5_s : String := "98 76"
def test5_Expected : Bool := false

-- Test case 6: single digit

def test6_s : String := "5"
def test6_Expected : Bool := true

-- Test case 7: single non-digit punctuation

def test7_s : String := "+"
def test7_Expected : Bool := false

-- Test case 8: newline character present

def test8_s : String := "12\n34"
def test8_Expected : Bool := false

-- Test case 9: mixed punctuation and digits

def test9_s : String := "12-34"
def test9_Expected : Bool := false

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test2, test3

end TestCases
