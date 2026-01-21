/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 47bb0548-8a0c-4823-af78-6d77c7ea08fb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) (oldChar : Char) (newChar : Char):
  VerinaSpec.replaceChars_precond s oldChar newChar ↔ LeetProofSpec.precondition s oldChar newChar

- theorem postcondition_equiv (s : String) (oldChar : Char) (newChar : Char) (result : String) (h_precond : VerinaSpec.replaceChars_precond s oldChar newChar):
  VerinaSpec.replaceChars_postcond s oldChar newChar result h_precond ↔ LeetProofSpec.postcondition s oldChar newChar result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def replaceChars_precond (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def replaceChars_postcond (s : String) (oldChar : Char) (newChar : Char) (result: String) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < cs.length →
    (cs[i]! = oldChar → cs'[i]! = newChar) ∧
    (cs[i]! ≠ oldChar → cs'[i]! = cs[i]!))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input
def precondition (s : String) (oldChar : Char) (newChar : Char) :=
  True

-- Postcondition: Specifies the character replacement properties
-- 1. Result has the same length as input
-- 2. For each position i:
--    - If input[i] = oldChar, then result[i] = newChar
--    - Otherwise, result[i] = input[i] (unchanged)
def postcondition (s : String) (oldChar : Char) (newChar : Char) (result : String) :=
  result.length = s.length ∧
  ∀ i : Nat, i < s.length →
    (s.toList[i]! = oldChar → result.toList[i]! = newChar) ∧
    (s.toList[i]! ≠ oldChar → result.toList[i]! = s.toList[i]!)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String) (oldChar : Char) (newChar : Char):
  VerinaSpec.replaceChars_precond s oldChar newChar ↔ LeetProofSpec.precondition s oldChar newChar := by
  -- Since both preconditions are True, the equivalence is trivially true.
  simp [VerinaSpec.replaceChars_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (oldChar : Char) (newChar : Char) (result : String) (h_precond : VerinaSpec.replaceChars_precond s oldChar newChar):
  VerinaSpec.replaceChars_postcond s oldChar newChar result h_precond ↔ LeetProofSpec.postcondition s oldChar newChar result := by
  exact?