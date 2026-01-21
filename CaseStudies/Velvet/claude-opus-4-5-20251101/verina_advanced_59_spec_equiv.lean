/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 91e94f3c-c98b-4874-8dde-ace5d8f46d06

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.palindromeIgnoreNonAlnum_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.palindromeIgnoreNonAlnum_precond s):
  VerinaSpec.palindromeIgnoreNonAlnum_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def palindromeIgnoreNonAlnum_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def palindromeIgnoreNonAlnum_postcond (s : String) (result: Bool) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Prop :=
  -- !benchmark @start postcond
  let cleaned := s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower
let forward := cleaned
let backward := cleaned.reverse

if result then
  forward = backward
else
  forward ≠ backward

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Extract alphanumeric characters and convert to lowercase
def normalizedChars (s : String) : List Char :=
  (s.toList.filter Char.isAlphanum).map Char.toLower

-- Postcondition: the result is true if and only if the normalized character list is a palindrome
def postcondition_clause (s : String) (result : Bool) :=
  let normalized := normalizedChars s
  result = (normalized == normalized.reverse)

def precondition (s : String) :=
  True

-- no preconditions

def postcondition (s : String) (result : Bool) :=
  postcondition_clause s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.palindromeIgnoreNonAlnum_precond s ↔ LeetProofSpec.precondition s := by
  exact iff_of_true trivial trivial

theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.palindromeIgnoreNonAlnum_precond s):
  VerinaSpec.palindromeIgnoreNonAlnum_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- By definition of `postcondition`, we know that if the result is true, then the normalized list is equal to its reverse, and if the result is false, then the normalized list is not equal to its reverse.
  simp [VerinaSpec.palindromeIgnoreNonAlnum_postcond, LeetProofSpec.postcondition];
  -- By definition of `postcondition_clause`, we know that if the result is true, then the normalized list is equal to its reverse, and if the result is false, then the normalized list is not equal to its reverse.
  simp [LeetProofSpec.postcondition_clause];
  aesop