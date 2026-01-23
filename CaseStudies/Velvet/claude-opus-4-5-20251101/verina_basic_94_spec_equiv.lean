/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d3e7a8a7-319f-4508-8c4d-236cb4d4b473

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : Array Int):
  VerinaSpec.iter_copy_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : Array Int) (result : Array Int) (h_precond : VerinaSpec.iter_copy_precond s):
  VerinaSpec.iter_copy_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def iter_copy_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def iter_copy_postcond (s : Array Int) (result: Array Int) (h_precond : iter_copy_precond (s)) :=
  -- !benchmark @start postcond
  (s.size = result.size) ∧ (∀ i : Nat, i < s.size → s[i]! = result[i]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No special requirements, any array is valid input
def precondition (s : Array Int) : Prop :=
  True

-- Postcondition: The result array is identical to the input array
-- This means same size and same elements at each position
def postcondition (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  ∀ i : Nat, i < s.size → result[i]! = s[i]!

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : Array Int):
  VerinaSpec.iter_copy_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are true, the equivalence is immediate.
  simp [VerinaSpec.iter_copy_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : Array Int) (result : Array Int) (h_precond : VerinaSpec.iter_copy_precond s):
  VerinaSpec.iter_copy_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- The equivalence follows directly from the definitions of the postconditions.
  simp [VerinaSpec.iter_copy_postcond, LeetProofSpec.postcondition];
  -- Since equality is symmetric, the two statements are equivalent.
  simp [eq_comm]