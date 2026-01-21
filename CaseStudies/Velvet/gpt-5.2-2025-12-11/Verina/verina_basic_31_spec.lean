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
    toUppercase: Convert a string to uppercase.
    Natural language breakdown:
    1. Input is a string s.
    2. Output is a string result.
    3. The output has the same length as the input.
    4. For every position i within bounds, the i-th character of result equals
       the uppercase of the i-th character of s.
    5. Uppercasing is performed using Char.toUpper: lowercase ASCII letters are
       mapped to their corresponding uppercase letters; all other characters are unchanged.
    6. There are no preconditions.
-/

section Specs

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  result.length = s.length ∧
    (∀ (i : Nat), i < s.length → result.toList[i]! = (s.toList[i]!).toUpper)

end Specs

section Impl

method toUppercase (s: String)
  return (result: String)
  require precondition s
  ensures postcondition s result
  do
  pure ""  -- placeholder

end Impl

section TestCases

-- Test case 1: provided example
-- "Hello, World!" → "HELLO, WORLD!"
def test1_s : String := "Hello, World!"
def test1_Expected : String := "HELLO, WORLD!"

-- Test case 2: all lowercase
def test2_s : String := "abc"
def test2_Expected : String := "ABC"

-- Test case 3: already uppercase
def test3_s : String := "ABC"
def test3_Expected : String := "ABC"

-- Test case 4: non-letters unchanged
def test4_s : String := "123!?@"
def test4_Expected : String := "123!?@"

-- Test case 5: empty string
def test5_s : String := ""
def test5_Expected : String := ""

-- Test case 6: mixed with whitespace and newlines
def test6_s : String := "a Z\n\t!"
def test6_Expected : String := "A Z\n\t!"

-- Test case 7: letters near ASCII boundaries
def test7_s : String := "xyzXYZ"
def test7_Expected : String := "XYZXYZ"

-- Test case 8: punctuation around letters
def test8_s : String := "(lean4)"
def test8_Expected : String := "(LEAN4)"

-- Test case 9: repeating letters and mixed case
def test9_s : String := "aAaA"
def test9_Expected : String := "AAAA"

-- Recommend to validate: test1, test2, test5

end TestCases
