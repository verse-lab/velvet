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
    toLowercase: Convert all uppercase characters in a string to their lowercase equivalents.
    Natural language breakdown:
    1. Input is any string s (no preconditions).
    2. Output is a string result with the same length as s.
    3. For every character position i in s, the output character at i equals Char.toLower applied to the input character at i.
    4. Characters not affected by Char.toLower remain unchanged.
-/

section Specs

-- Helper: Pointwise character relation between two strings via their underlying Char lists.
-- This characterizes the output uniquely without referring to String.toLower.
-- Note: Char.toLower converts uppercase ASCII letters 'A'..'Z' to lowercase and leaves other chars unchanged.
def charsLoweredPointwise (s : String) (t : String) : Prop :=
  let sl := s.toList
  let tl := t.toList
  tl.length = sl.length ∧
    ∀ (i : Nat), i < sl.length → tl[i]! = Char.toLower (sl[i]!)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  charsLoweredPointwise s result

end Specs

section Impl

method toLowercase (s: String)
  return (result: String)
  require precondition s
  ensures postcondition s result
  do
  pure ""  -- placeholder

end Impl

section TestCases

-- Test case 1: provided example with punctuation and mixed case
-- "Hello, World!" → "hello, world!"
def test1_s : String := "Hello, World!"
def test1_Expected : String := "hello, world!"

-- Test case 2: all uppercase

def test2_s : String := "ABC"
def test2_Expected : String := "abc"

-- Test case 3: already lowercase

def test3_s : String := "abc"
def test3_Expected : String := "abc"

-- Test case 4: empty string

def test4_s : String := ""
def test4_Expected : String := ""

-- Test case 5: digits and symbols only

def test5_s : String := "1234!@"
def test5_Expected : String := "1234!@"

-- Test case 6: mixed case with digits

def test6_s : String := "MixedCASE123"
def test6_Expected : String := "mixedcase123"

-- Test case 7: single uppercase character

def test7_s : String := "Z"
def test7_Expected : String := "z"

-- Test case 8: whitespace and newline preserved

def test8_s : String := "A a\nB"
def test8_Expected : String := "a a\nb"

-- Test case 9: non-ASCII letter (Char.toLower leaves it unchanged)

def test9_s : String := "É"
def test9_Expected : String := "É"

-- Recommend to validate: test1, test4, test6

end TestCases
