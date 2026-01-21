/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 962fe636-22d1-488a-a450-c08c1dccf964

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (words_str : String):
  VerinaSpec.reverseWords_precond words_str ↔ LeetProofSpec.precondition words_str
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def reverseWords_precond (words_str : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def reverseWords_postcond (words_str : String) (result: String) (h_precond : reverseWords_precond (words_str)) : Prop :=
  -- !benchmark @start postcond
  ∃ words : List String,
    (words = (words_str.splitOn " ").filter (fun w => w ≠ "")) ∧
    result = String.intercalate " " (words.reverse)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Extract words from a string (splitting by spaces, filtering empty strings)
def extractWords (s : String) : List String :=
  (s.split (· = ' ')).filter (· ≠ "")

-- Check if a string has no leading spaces
def noLeadingSpaces (s : String) : Bool :=
  s.data.head? ≠ some ' '

-- Check if a string has no trailing spaces
def noTrailingSpaces (s : String) : Bool :=
  s.data.getLast? ≠ some ' '

-- Check if there are no consecutive spaces in a string
def noConsecutiveSpaces (s : String) : Bool :=
  let chars := s.data
  chars.length < 2 ∨ (List.zip chars chars.tail).all (fun (a, b) => ¬(a = ' ' ∧ b = ' '))

-- Check if the result is properly formatted (no leading/trailing/consecutive spaces)
def isProperlyFormatted (s : String) : Bool :=
  s = "" ∨ (noLeadingSpaces s ∧ noTrailingSpaces s ∧ noConsecutiveSpaces s)

-- Postcondition clauses

-- The words in result are the reverse of words in input
def ensures1 (words_str : String) (result : String) : Prop :=
  extractWords result = (extractWords words_str).reverse

-- The result is properly formatted (no extra spaces)
def ensures2 (words_str : String) (result : String) : Prop :=
  isProperlyFormatted result

def precondition (words_str : String) : Prop :=
  True

-- no preconditions

def postcondition (words_str : String) (result : String) : Prop :=
  ensures1 words_str result ∧
  ensures2 words_str result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (words_str : String):
  VerinaSpec.reverseWords_precond words_str ↔ LeetProofSpec.precondition words_str := by
  -- Since both preconditions are True, they are trivially equivalent.
  simp [VerinaSpec.reverseWords_precond, LeetProofSpec.precondition]

/- Aristotle failed to find a proof. -/
theorem postcondition_equiv (words_str : String) (result : String) (h_precond : VerinaSpec.reverseWords_precond words_str):
  VerinaSpec.reverseWords_postcond words_str result h_precond ↔ LeetProofSpec.postcondition words_str result := by
  sorry
