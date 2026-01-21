import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    replaceWithColon: Replace every space, comma, or dot with a colon
    Natural language breakdown:
    1. Given a string s, produce a new string where certain characters are replaced
    2. The characters to be replaced are: space (' '), comma (','), and dot ('.')
    3. Each of these characters should be replaced with a colon (':')
    4. All other characters remain unchanged
    5. The result string must have the same length as the input string
    6. The transformation is position-wise: result[i] depends only on s[i]
    7. If s[i] is a space, comma, or dot, then result[i] = ':'
    8. If s[i] is any other character, then result[i] = s[i]
-/

section Specs

-- Helper to check if a character should be replaced
def shouldReplace (c : Char) : Bool :=
  c = ' ' ∨ c = ',' ∨ c = '.'

-- Transform a single character according to the rule
def transformChar (c : Char) : Char :=
  if shouldReplace c then ':' else c

-- Postcondition clauses
-- The result has the same length as the input
def ensures1 (s : String) (result : String) : Prop :=
  result.length = s.length

-- Each character is transformed correctly: replaced if space/comma/dot, unchanged otherwise
def ensures2 (s : String) (result : String) : Prop :=
  ∀ i : Nat, i < s.length →
    result.data[i]! = transformChar s.data[i]!

def precondition (s : String) : Prop :=
  True  -- no preconditions

def postcondition (s : String) (result : String) : Prop :=
  ensures1 s result ∧
  ensures2 s result

end Specs

section Impl

method replaceWithColon (s : String)
  return (result : String)
  require precondition s
  ensures postcondition s result
  do
  pure ""  -- placeholder

end Impl

section TestCases

-- Test case 1: Example from problem - mixed spaces, commas, and dots
def test1_s : String := "Hello, world. How are you?"
def test1_Expected : String := "Hello::world::How:are:you?"

-- Test case 2: No replacements needed
def test2_s : String := "No-changes!"
def test2_Expected : String := "No-changes!"

-- Test case 3: All characters to be replaced
def test3_s : String := ",. "
def test3_Expected : String := ":::"

-- Test case 4: Empty string
def test4_s : String := ""
def test4_Expected : String := ""

-- Test case 5: Only spaces
def test5_s : String := "   "
def test5_Expected : String := ":::"

-- Test case 6: Only dots
def test6_s : String := "..."
def test6_Expected : String := ":::"

-- Test case 7: Only commas
def test7_s : String := ",,,"
def test7_Expected : String := ":::"

-- Test case 8: Single character - space
def test8_s : String := " "
def test8_Expected : String := ":"

-- Test case 9: Single character - regular letter
def test9_s : String := "a"
def test9_Expected : String := "a"

-- Test case 10: Mixed with numbers and special chars
def test10_s : String := "a.b,c d!@#"
def test10_Expected : String := "a:b:c:d!@#"

-- Recommend to validate: 1, 3, 4

end TestCases
