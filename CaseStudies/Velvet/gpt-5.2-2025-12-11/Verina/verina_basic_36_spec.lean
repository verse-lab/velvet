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
    replaceWithColon: Replace each space, comma, or dot character in a string with a colon.
    Natural language breakdown:
    1. Input is a single string s.
    2. Output is a string result.
    3. The output and input have the same number of characters (as lists of Char).
    4. For each character position i within s.toList.length:
       - If the input character is ' ' or ',' or '.', then the output character is ':'.
       - Otherwise, the output character equals the input character.
    5. All characters not in the set {space, comma, dot} remain unchanged.
    6. There are no preconditions.
-/

section Specs

-- Helper: the set of characters to be replaced.
def shouldReplaceWithColon (c : Char) : Bool :=
  c = ' ' || c = ',' || c = '.'

-- Helper: pointwise character relation between input/output at an index.
def charSpecAt (s : String) (result : String) (i : Nat) : Prop :=
  i < s.toList.length →
    let cin := s.toList[i]!
    let cout := result.toList[i]!
    (shouldReplaceWithColon cin = true → cout = ':') ∧
    (shouldReplaceWithColon cin = false → cout = cin)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  result.toList.length = s.toList.length ∧
  ∀ i : Nat, charSpecAt s result i

end Specs

section Impl

method replaceWithColon (s : String) return (result : String)
  require precondition s
  ensures postcondition s result
  do
  pure ""  -- placeholder

end Impl

section TestCases

-- Test case 1: example from prompt
-- "Hello, world. How are you?" -> "Hello::world::How:are:you?"
def test1_s : String := "Hello, world. How are you?"
def test1_Expected : String := "Hello::world::How:are:you?"

-- Test case 2: no characters to replace
-- "No-changes!" stays the same
def test2_s : String := "No-changes!"
def test2_Expected : String := "No-changes!"

-- Test case 3: only replaceable characters
-- ",. " -> ":::"
def test3_s : String := ",. "
def test3_Expected : String := ":::"

-- Test case 4: empty string
def test4_s : String := ""
def test4_Expected : String := ""

-- Test case 5: single replaceable character: space
def test5_s : String := " "
def test5_Expected : String := ":"

-- Test case 6: single replaceable character: comma
def test6_s : String := ","
def test6_Expected : String := ":"

-- Test case 7: single replaceable character: dot
def test7_s : String := "."
def test7_Expected : String := ":"

-- Test case 8: mixture with consecutive punctuation and internal spaces
def test8_s : String := "a, b.c"
def test8_Expected : String := "a::b:c"

-- Test case 9: other punctuation should remain unchanged (question mark, exclamation)
def test9_s : String := "?.!?"
def test9_Expected : String := "?:!?"

-- Recommend to validate: 1, 3, 8

end TestCases
