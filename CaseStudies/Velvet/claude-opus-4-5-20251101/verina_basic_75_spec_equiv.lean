/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d94f8909-e36b-4ac3-a1e2-956271ab2cff

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.minArray_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.minArray_precond a):
  VerinaSpec.minArray_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def minArray_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0

-- !benchmark @end precond

def loop (a : Array Int) (i : Nat) (currentMin : Int) : Int :=
  if i < a.size then
    let newMin := if currentMin > a[i]! then a[i]! else currentMin
    loop a (i + 1) newMin
  else
    currentMin

def minArray_postcond (a : Array Int) (result: Int) (h_precond : minArray_precond (a)) :=
  -- !benchmark @start postcond
  (∀ i : Nat, i < a.size → result <= a[i]!) ∧ (∃ i : Nat, i < a.size ∧ result = a[i]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: array must be non-empty
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: result is the minimum element
-- 1. result is less than or equal to all elements in the array
-- 2. result is equal to at least one element in the array (membership)
def postcondition (a : Array Int) (result : Int) : Prop :=
  (∀ i : Nat, i < a.size → result ≤ a[i]!) ∧
  (∃ j : Nat, j < a.size ∧ a[j]! = result)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.minArray_precond a ↔ LeetProofSpec.precondition a := by
  -- The preconditions are identical, so the equivalence holds trivially.
  simp [VerinaSpec.minArray_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.minArray_precond a):
  VerinaSpec.minArray_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- The two postconditions are equivalent because they both require the result to be the minimum element in the array.
  simp [VerinaSpec.minArray_postcond, LeetProofSpec.postcondition];
  -- The equivalence follows from the symmetry of equality.
  intros h
  simp [eq_comm]