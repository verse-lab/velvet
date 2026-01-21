import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    allDigits: Determine whether every character in a string is a digit
    Natural language breakdown:
    1. The function takes a string as input
    2. A digit is defined as a character in the range '0' to '9'
    3. The function returns true if and only if every character in the string is a digit
    4. The function returns false if at least one character is not a digit
    5. For an empty string, the function returns true (vacuous truth - no characters to fail)
    6. Uses Char.isDigit to check if a character is a digit
-/

section Specs

-- Helper Functions
-- Using String.all from Mathlib/Init which checks if all characters satisfy a predicate
-- Using Char.isDigit which checks if a character is a digit ('0' to '9')

-- Postcondition: result is true iff all characters are digits
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ s.all Char.isDigit = true

-- Alternative characterization: result matches String.all with isDigit predicate
def ensures2 (s : String) (result : Bool) :=
  result = s.all Char.isDigit

def precondition (s : String) :=
  True  -- no preconditions needed

def postcondition (s : String) (result : Bool) :=
  ensures2 s result

end Specs

section Impl

method allDigits (s: String)
  return (result: Bool)
  require precondition s
  ensures postcondition s result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: All digits (from problem examples)
def test1_s : String := "123456"
def test1_Expected : Bool := true

-- Test case 2: Contains a letter (from problem examples)
def test2_s : String := "123a56"
def test2_Expected : Bool := false

-- Test case 3: Empty string (from problem examples)
def test3_s : String := ""
def test3_Expected : Bool := true

-- Test case 4: Leading zeros (from problem examples)
def test4_s : String := "007"
def test4_Expected : Bool := true

-- Test case 5: Contains space (from problem examples)
def test5_s : String := "98 76"
def test5_Expected : Bool := false

-- Test case 6: Single digit
def test6_s : String := "5"
def test6_Expected : Bool := true

-- Test case 7: Single non-digit character
def test7_s : String := "x"
def test7_Expected : Bool := false

-- Test case 8: All same digit
def test8_s : String := "0000"
def test8_Expected : Bool := true

-- Test case 9: Special characters mixed with digits
def test9_s : String := "12-34"
def test9_Expected : Bool := false

-- Test case 10: Long string of digits
def test10_s : String := "9876543210"
def test10_Expected : Bool := true

-- Recommend to validate: 1, 2, 3

end TestCases
