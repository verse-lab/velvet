import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findFirstRepeatedChar: Find the first character in a string that appears more than once
    Natural language breakdown:
    1. Given a string s, we need to find the first repeated character
    2. A character is "repeated" if it appears at least twice in the string
    3. The "first repeated" character is the one whose second occurrence comes earliest
    4. More precisely: we look at each position i, and check if s[i] has appeared before (in positions 0..i-1)
    5. The result is the character at the smallest such position i where s[i] appeared earlier
    6. If no character repeats, return none
    7. If a character repeats, return some c where c is that first repeated character
    8. Empty strings and strings with all unique characters return none
    9. Case sensitive: 'A' and 'a' are different characters
-/

section Specs

-- Helper: Check if character c appears in the list before position i
def appearsBeforePos (chars : List Char) (c : Char) (i : Nat) : Prop :=
  ∃ j : Nat, j < i ∧ j < chars.length ∧ chars[j]! = c

-- Helper: Position i is where we first see a repeated character
-- (chars[i] appeared somewhere before position i, and no earlier position has this property)
def isFirstRepeatPos (chars : List Char) (i : Nat) : Prop :=
  i < chars.length ∧
  appearsBeforePos chars chars[i]! i ∧
  ∀ k : Nat, k < i → ¬appearsBeforePos chars chars[k]! k

-- Helper: Check if any character in the string is repeated
def hasRepeatedChar (chars : List Char) : Prop :=
  ∃ i : Nat, i < chars.length ∧ appearsBeforePos chars chars[i]! i

-- Postcondition clause 1: If result is some c, then c is a repeated character found at the first repeat position
def ensures1 (s : String) (result : Option Char) :=
  ∀ c : Char, result = some c →
    ∃ i : Nat, isFirstRepeatPos s.toList i ∧ s.toList[i]! = c

-- Postcondition clause 2: If result is none, then no character repeats in the string
def ensures2 (s : String) (result : Option Char) :=
  result = none → ¬hasRepeatedChar s.toList

-- Postcondition clause 3: If there is a repeated character, result must be some
def ensures3 (s : String) (result : Option Char) :=
  hasRepeatedChar s.toList → result.isSome

def precondition (s : String) :=
  True  -- no preconditions

def postcondition (s : String) (result : Option Char) :=
  ensures1 s result ∧
  ensures2 s result ∧
  ensures3 s result

end Specs

section Impl

method findFirstRepeatedChar (s : String)
  return (result : Option Char)
  require precondition s
  ensures postcondition s result
  do
  pure none  -- placeholder

end Impl

section TestCases

-- Test case 1: "abca" - 'a' repeats, first repeat is at position 3
def test1_s : String := "abca"
def test1_Expected : Option Char := some 'a'

-- Test case 2: "abcdef" - no repeats
def test2_s : String := "abcdef"
def test2_Expected : Option Char := none

-- Test case 3: "aabbcc" - 'a' repeats first at position 1
def test3_s : String := "aabbcc"
def test3_Expected : Option Char := some 'a'

-- Test case 4: "" - empty string, no repeats
def test4_s : String := ""
def test4_Expected : Option Char := none

-- Test case 5: "abbc" - 'b' repeats first at position 2
def test5_s : String := "abbc"
def test5_Expected : Option Char := some 'b'

-- Test case 6: "Aa" - case sensitive, 'A' ≠ 'a', no repeats
def test6_s : String := "Aa"
def test6_Expected : Option Char := none

-- Test case 7: "a" - single character, no repeat possible
def test7_s : String := "a"
def test7_Expected : Option Char := none

-- Test case 8: "aa" - 'a' repeats at position 1
def test8_s : String := "aa"
def test8_Expected : Option Char := some 'a'

-- Test case 9: "abcba" - 'b' repeats at position 3, 'a' repeats at position 4, first is 'b'
def test9_s : String := "abcba"
def test9_Expected : Option Char := some 'b'

-- Test case 10: "xyzxabc" - 'x' repeats at position 3
def test10_s : String := "xyzxabc"
def test10_Expected : Option Char := some 'x'

-- Recommend to validate: 1, 3, 5

end TestCases
