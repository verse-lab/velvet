/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 46e8b9fa-c7b4-4321-9eb9-2b9822b5286d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.isCleanPalindrome_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.isCleanPalindrome_precond s):
  VerinaSpec.isCleanPalindrome_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

-- Check if a character is an uppercase alphabet letter
def isUpperAlpha (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

-- Check if a character is a lowercase alphabet letter
def isLowerAlpha (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

-- Determine if a character is alphabetic
def isAlpha (c : Char) : Bool :=
  isUpperAlpha c ∨ isLowerAlpha c

-- Convert a single character to lowercase
def toLower (c : Char) : Char :=
  if isUpperAlpha c then Char.ofNat (c.toNat + 32) else c

-- Normalize a character: keep only lowercase letters
def normalizeChar (c : Char) : Option Char :=
  if isAlpha c then some (toLower c) else none

-- Normalize a string into a list of lowercase alphabetic characters
def normalizeString (s : String) : List Char :=
  s.toList.foldr (fun c acc =>
    match normalizeChar c with
    | some c' => c' :: acc
    | none    => acc
  ) []

@[reducible]
def isCleanPalindrome_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

-- Reverse the list
def reverseList (xs : List Char) : List Char :=
  xs.reverse

@[reducible]
def isCleanPalindrome_postcond (s : String) (result: Bool) (h_precond : isCleanPalindrome_precond (s)) : Prop :=
  -- !benchmark @start postcond
  let norm := normalizeString s
  (result = true → norm = norm.reverse) ∧
  (result = false → norm ≠ norm.reverse)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Filter to keep only alphabetic characters and convert to lowercase
def cleanString (s : String) : List Char :=
  (s.toList.filter Char.isAlpha).map Char.toLower

-- Check if a list is a palindrome (equals its reverse)
def isPalindrome (chars : List Char) : Prop :=
  chars = chars.reverse

-- Postcondition clauses
-- The result is true if and only if the cleaned string is a palindrome
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ cleanString s = (cleanString s).reverse

def precondition (s : String) :=
  True

-- no preconditions

def postcondition (s : String) (result : Bool) :=
  ensures1 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.isCleanPalindrome_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are True, the equivalence holds trivially.
  simp [VerinaSpec.isCleanPalindrome_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.isCleanPalindrome_precond s):
  VerinaSpec.isCleanPalindrome_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- By definition of `normalizeString`, we know that `normalizeString s` is equal to `cleanString s`.
  have h_normalize : VerinaSpec.normalizeString s = LeetProofSpec.cleanString s := by
    -- Apply the definition of `normalizeString` and `cleanString` to show they are equal.
    simp [VerinaSpec.normalizeString, LeetProofSpec.cleanString];
    -- By definition of `normalizeChar`, we know that it is equivalent to `Char.toLower` if the character is alphabetic, and `none` otherwise.
    have h_normalizeChar : ∀ c : Char, VerinaSpec.normalizeChar c = if Char.isAlpha c then some (Char.toLower c) else none := by
      unfold VerinaSpec.normalizeChar;
      unfold VerinaSpec.isAlpha VerinaSpec.toLower; simp +decide [ Char.isAlpha ] ;
      unfold VerinaSpec.isUpperAlpha VerinaSpec.isLowerAlpha Char.isUpper Char.isLower; aesop;
    induction s.data <;> aesop;
  unfold VerinaSpec.isCleanPalindrome_postcond LeetProofSpec.postcondition;
  cases result <;> simp +decide [ h_normalize, LeetProofSpec.ensures1 ]