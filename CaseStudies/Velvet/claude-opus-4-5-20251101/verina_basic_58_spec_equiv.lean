/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9d933dde-8605-4a86-b8db-7c1d45405eb7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : Array Int):
  VerinaSpec.double_array_elements_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : Array Int) (result : Array Int) (h_precond : VerinaSpec.double_array_elements_precond s):
  VerinaSpec.double_array_elements_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def double_array_elements_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def double_array_elements_aux (s_old s : Array Int) (i : Nat) : Array Int :=
  if i < s.size then
    let new_s := s.set! i (2 * (s_old[i]!))
    double_array_elements_aux s_old new_s (i + 1)
  else
    s

def double_array_elements_postcond (s : Array Int) (result: Array Int) (h_precond : double_array_elements_precond (s)) :=
  -- !benchmark @start postcond
  result.size = s.size ∧ ∀ i, i < s.size → result[i]! = 2 * s[i]!

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: no special requirements on the input array
def precondition (s : Array Int) : Prop :=
  True

-- Postcondition: result has same size and each element is doubled
def postcondition (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  ∀ i : Nat, i < s.size → result[i]! = 2 * s[i]!

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : Array Int):
  VerinaSpec.double_array_elements_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are True, the equivalence is trivially true.
  simp [VerinaSpec.double_array_elements_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : Array Int) (result : Array Int) (h_precond : VerinaSpec.double_array_elements_precond s):
  VerinaSpec.double_array_elements_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- Since the preconditions are equivalent, the postconditions are also equivalent.
  simp [VerinaSpec.double_array_elements_postcond, LeetProofSpec.postcondition]