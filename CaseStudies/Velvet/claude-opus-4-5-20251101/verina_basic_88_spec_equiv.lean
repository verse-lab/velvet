/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a3489125-20ae-49fd-b71b-e9c95ebdae78

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int):
  VerinaSpec.ToArray_precond xs ↔ LeetProofSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : Array Int) (h_precond : VerinaSpec.ToArray_precond xs):
  VerinaSpec.ToArray_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def ToArray_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def ToArray_postcond (xs : List Int) (result: Array Int) (h_precond : ToArray_precond (xs)) :=
  -- !benchmark @start postcond
  result.size = xs.length ∧ ∀ (i : Nat), i < xs.length → result[i]! = xs[i]!

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No requirements, any list is valid input
def precondition (xs : List Int) :=
  True

-- Postcondition: Array has same size as list length, and each element matches
def postcondition (xs : List Int) (result : Array Int) :=
  result.size = xs.length ∧
  ∀ i : Nat, i < xs.length → result[i]! = xs[i]!

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (xs : List Int):
  VerinaSpec.ToArray_precond xs ↔ LeetProofSpec.precondition xs := by
  -- Since both preconditions are True, the equivalence holds by definition.
  simp [VerinaSpec.ToArray_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (xs : List Int) (result : Array Int) (h_precond : VerinaSpec.ToArray_precond xs):
  VerinaSpec.ToArray_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result := by
  -- The postconditions are equivalent because they both require the array's size to match the list's length and each element to match the corresponding element in the list.
  simp [VerinaSpec.ToArray_postcond, LeetProofSpec.postcondition]