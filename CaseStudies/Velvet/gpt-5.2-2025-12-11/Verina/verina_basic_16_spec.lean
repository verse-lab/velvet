import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import Mathlib.Data.String.Basic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    replaceChars: Replace every occurrence of a specified character in a string.
    Natural language breakdown:
    1. Inputs are a string s and two characters oldChar and newChar.
    2. The result is a string with the same number of characters as s.
    3. For each index i within bounds, if the i-th character of s equals oldChar,
       then the i-th character of the result equals newChar.
    4. For each index i within bounds, if the i-th character of s does not equal oldChar,
       then the i-th character of the result equals the i-th character of s.
    5. There are no preconditions; the method must work for any string and characters.
-/

section Specs

-- Helper: pointwise replacement on characters.
-- This is a simple, computable predicate used in the postcondition.
def replChar (oldChar : Char) (newChar : Char) (c : Char) : Char :=
  if c = oldChar then newChar else c

-- No preconditions.
def precondition (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  True

-- Postcondition: list-view length preserved and pointwise replacement behavior on `toList`.
-- We specify everything through `toList` to avoid mixing different views (`String.length` vs list length).
def postcondition (s : String) (oldChar : Char) (newChar : Char) (result : String) : Prop :=
  result.toList.length = s.toList.length ∧
  (∀ (i : Nat), i < s.toList.length →
    result.toList[i]! = replChar oldChar newChar (s.toList[i]!))

end Specs

section Impl

method replaceChars (s : String) (oldChar : Char) (newChar : Char)
  return (result : String)
  require precondition s oldChar newChar
  ensures postcondition s oldChar newChar result
  do
  pure s  -- placeholder body

end Impl

section TestCases

-- Test case 1: example from prompt

def test1_s : String := "hello, world!"
def test1_oldChar : Char := ','
def test1_newChar : Char := ';'
def test1_Expected : String := "hello; world!"

-- Test case 2: punctuation replacement inside string

def test2_s : String := "a,b.c"
def test2_oldChar : Char := ','
def test2_newChar : Char := ':'
def test2_Expected : String := "a:b.c"

-- Test case 3: multiple occurrences of a letter

def test3_s : String := "hello, world!"
def test3_oldChar : Char := 'o'
def test3_newChar : Char := 'O'
def test3_Expected : String := "hellO, wOrld!"

-- Test case 4: empty string

def test4_s : String := ""
def test4_oldChar : Char := 'x'
def test4_newChar : Char := 'y'
def test4_Expected : String := ""

-- Test case 5: oldChar not present

def test5_s : String := "test"
def test5_oldChar : Char := 'x'
def test5_newChar : Char := 'y'
def test5_Expected : String := "test"

-- Test case 6: oldChar equals newChar (idempotent)

def test6_s : String := "unchanged"
def test6_oldChar : Char := 'u'
def test6_newChar : Char := 'u'
def test6_Expected : String := "unchanged"

-- Test case 7: all characters replaced

def test7_s : String := "aaa"
def test7_oldChar : Char := 'a'
def test7_newChar : Char := 'b'
def test7_Expected : String := "bbb"

-- Test case 8: single-character string replaced

def test8_s : String := "x"
def test8_oldChar : Char := 'x'
def test8_newChar : Char := 'y'
def test8_Expected : String := "y"

-- Test case 9: single-character string unchanged

def test9_s : String := "x"
def test9_oldChar : Char := 'z'
def test9_newChar : Char := 'y'
def test9_Expected : String := "x"

-- Recommend to validate: test1, test3, test7

end TestCases
