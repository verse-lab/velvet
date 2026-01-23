/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2a71bb3d-77ac-47af-9731-0c8af92d19c7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (P : Int -> Bool):
  VerinaSpec.LinearSearch3_precond a P ↔ LeetProofSpec.precondition a P

- theorem postcondition_equiv (a : Array Int) (P : Int -> Bool) (result : Nat) (h_precond : VerinaSpec.LinearSearch3_precond a P):
  VerinaSpec.LinearSearch3_postcond a P result h_precond ↔ LeetProofSpec.postcondition a P result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def LinearSearch3_precond (a : Array Int) (P : Int -> Bool) : Prop :=
  -- !benchmark @start precond
  ∃ i, i < a.size ∧ P (a[i]!)

-- !benchmark @end precond

def LinearSearch3_postcond (a : Array Int) (P : Int -> Bool) (result: Nat) (h_precond : LinearSearch3_precond (a) (P)) :=
  -- !benchmark @start postcond
  result < a.size ∧ P (a[result]!) ∧ (∀ k, k < result → ¬ P (a[k]!))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: array is non-empty and at least one element satisfies P
def precondition (a : Array Int) (P : Int → Bool) :=
  ∃ i : Nat, i < a.size ∧ P (a[i]!) = true

-- Postcondition: result is the first index where P holds
-- 1. result is a valid index (less than array size)
-- 2. the element at result satisfies P
-- 3. all elements before result do not satisfy P
def postcondition (a : Array Int) (P : Int → Bool) (result : Nat) :=
  result < a.size ∧
  P (a[result]!) = true ∧
  (∀ j : Nat, j < result → P (a[j]!) = false)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (P : Int -> Bool):
  VerinaSpec.LinearSearch3_precond a P ↔ LeetProofSpec.precondition a P := by
  -- The two preconditions are equivalent because they both state that there exists an index i such that i is less than the size of the array and P(a[i]!) holds.
  simp [VerinaSpec.LinearSearch3_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Array Int) (P : Int -> Bool) (result : Nat) (h_precond : VerinaSpec.LinearSearch3_precond a P):
  VerinaSpec.LinearSearch3_postcond a P result h_precond ↔ LeetProofSpec.postcondition a P result := by
  unfold VerinaSpec.LinearSearch3_postcond LeetProofSpec.postcondition; aesop