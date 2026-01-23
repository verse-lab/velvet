/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 51b67d60-739c-45b9-9fb7-f0bb111be308

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.countDigits_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Nat) (h_precond : VerinaSpec.countDigits_precond s):
  VerinaSpec.countDigits_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

def countDigits_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def countDigits_postcond (s : String) (result: Nat) (h_precond : countDigits_precond (s)) :=
  -- !benchmark @start postcond
  result - List.length (List.filter isDigit s.toList) = 0 ∧
  List.length (List.filter isDigit s.toList) - result = 0

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: no constraints on input
def precondition (s : String) :=
  True

-- Postcondition: result equals the count of digit characters in the string
-- Using List.countP with Char.isDigit predicate
def postcondition (s : String) (result : Nat) :=
  result = s.toList.countP (fun c => c.isDigit)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.countDigits_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are True, the equivalence holds trivially.
  simp [VerinaSpec.countDigits_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (result : Nat) (h_precond : VerinaSpec.countDigits_precond s):
  VerinaSpec.countDigits_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- By definition of `countDigits_postcond`, we have `result - List.length (List.filter isDigit s.toList) = 0 ∧ List.length (List.filter isDigit s.toList) - result = 0`.
  simp [VerinaSpec.countDigits_postcond, LeetProofSpec.postcondition];
  -- The count of digits in the string is equal to the length of the filtered list.
  have h_count_eq_length : List.countP (fun c => c.isDigit) s.data = (List.filter VerinaSpec.isDigit s.data).length := by
    rw [ List.countP_eq_length_filter ];
    unfold VerinaSpec.isDigit; congr; ext; aesop;
  grind