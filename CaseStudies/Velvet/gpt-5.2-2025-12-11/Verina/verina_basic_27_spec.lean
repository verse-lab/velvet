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
    findFirstRepeatedChar: identify the first repeated character in a given string.
    Natural language breakdown:
    1. Input is a String s.
    2. Output is Option Char.
    3. Return none iff no character appears at least twice in the string.
    4. Return some c iff there exists a first position j (the earliest second-occurrence position)
       such that the character at position j has already appeared at some earlier i < j, and c is
       exactly that character at position j.
    5. “First repeated character” means: among all indices j where a repeat happens, pick the
       smallest j; the output is the character at that index.
    6. There are no preconditions; the method must work for any string (including empty).
-/

section Specs

-- A repetition at index j means there is an earlier index i < j with the same character.
-- We model strings via their character list representation.

def repeatsAt (l : List Char) (j : Nat) : Prop :=
  j < l.length ∧ ∃ i : Nat, i < j ∧ l[i]! = l[j]!

-- No repetitions strictly before index j.

def noRepeatBefore (l : List Char) (j : Nat) : Prop :=
  ∀ k : Nat, k < j → ¬repeatsAt l k

-- There are no preconditions.

def precondition (s : String) : Prop :=
  True

-- Postcondition:
-- * result = none iff the string has no repeated character anywhere
-- * result = some c iff there exists a minimal index j where a repeat happens, and c = l[j]!

def postcondition (s : String) (result : Option Char) : Prop :=
  let l := s.toList
  (result = none ↔ (∀ j : Nat, ¬repeatsAt l j)) ∧
    (∀ c : Char,
      result = some c ↔
        (∃ j : Nat, repeatsAt l j ∧ noRepeatBefore l j ∧ l[j]! = c))

end Specs

section Impl

method findFirstRepeatedChar (s: String) return (result: Option Char)
  require precondition s
  ensures postcondition s result
  do
  pure none

end Impl

section TestCases

-- Test case 1: example given: "abca" -> first repeated is 'a'

def test1_s : String := "abca"
def test1_Expected : Option Char := some 'a'

-- Test case 2: no repeats

def test2_s : String := "abcdef"
def test2_Expected : Option Char := none

-- Test case 3: grouped repeats; earliest second occurrence is for 'a'

def test3_s : String := "aabbcc"
def test3_Expected : Option Char := some 'a'

-- Test case 4: empty string

def test4_s : String := ""
def test4_Expected : Option Char := none

-- Test case 5: first repeated is 'b'

def test5_s : String := "abbc"
def test5_Expected : Option Char := some 'b'

-- Test case 6: case sensitivity, no repeats

def test6_s : String := "Aa"
def test6_Expected : Option Char := none

-- Test case 7: single character

def test7_s : String := "z"
def test7_Expected : Option Char := none

-- Test case 8: repeats with punctuation

def test8_s : String := "!!?"
def test8_Expected : Option Char := some '!'

-- Test case 9: multiple candidates; choose the one whose second appearance is earliest
-- "abcbad": b repeats first (at index 3)

def test9_s : String := "abcbad"
def test9_Expected : Option Char := some 'b'

-- Recommend to validate: test1, test5, test9

end TestCases
