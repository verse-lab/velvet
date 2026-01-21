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
    allCharactersSame: check whether all characters in an input string are identical.
    Natural language breakdown:
    1. The input is a string s.
    2. The output is a Boolean.
    3. If s is empty, the output is true.
    4. If s has exactly one character, the output is true.
    5. If s has at least two characters, the output is true exactly when every character equals the first character.
    6. Otherwise (there exists a character that differs from the first), the output is false.
-/

section Specs

-- Helper: Boolean predicate that checks whether all elements of a list equal a given value.
-- Uses List.all from core.
-- Note: Char has DecidableEq, so equality is decidable and can be used directly as a Bool predicate.
def allEq (l : List Char) (c : Char) : Bool :=
  l.all (fun d => d = c)

-- Helper: spec-level expected behavior as a Bool, defined by cases on the character list.
def allCharactersSameSpec (s : String) : Bool :=
  match s.toList with
  | [] => true
  | c :: cs => allEq cs c

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Bool) : Prop :=
  result = true ↔ allCharactersSameSpec s = true

end Specs

section Impl

method allCharactersSame (s: String) return (result: Bool)
  require precondition s
  ensures postcondition s result
  do
  pure true

end Impl

section TestCases

-- Test case 1: example from prompt
-- "aaa" -> true

def test1_s : String := "aaa"
def test1_Expected : Bool := true

-- Test case 2: differing middle character
-- "aba" -> false

def test2_s : String := "aba"
def test2_Expected : Bool := false

-- Test case 3: empty string
-- "" -> true

def test3_s : String := ""
def test3_Expected : Bool := true

-- Test case 4: single character
-- "a" -> true

def test4_s : String := "a"
def test4_Expected : Bool := true

-- Test case 5: all same longer string
-- "bbbb" -> true

def test5_s : String := "bbbb"
def test5_Expected : Bool := true

-- Test case 6: one differing character in the middle
-- "bbab" -> false

def test6_s : String := "bbab"
def test6_Expected : Bool := false

-- Test case 7: two different characters
-- "ab" -> false

def test7_s : String := "ab"
def test7_Expected : Bool := false

-- Test case 8: includes whitespace; all characters are whitespace
-- "   " -> true

def test8_s : String := "   "
def test8_Expected : Bool := true

-- Test case 9: includes newline characters; all same
-- "\n\n" -> true

def test9_s : String := "\n\n"
def test9_Expected : Bool := true

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 2, 3

end TestCases
