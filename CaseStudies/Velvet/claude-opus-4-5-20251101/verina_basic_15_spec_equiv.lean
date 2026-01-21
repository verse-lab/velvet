/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a547d971-1e0d-4c84-b90f-783c3b42bd17

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.containsConsecutiveNumbers_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Bool) (h_precond : VerinaSpec.containsConsecutiveNumbers_precond a):
  VerinaSpec.containsConsecutiveNumbers_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def containsConsecutiveNumbers_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def containsConsecutiveNumbers_postcond (a : Array Int) (result: Bool) (h_precond : containsConsecutiveNumbers_precond (a)) :=
  -- !benchmark @start postcond
  (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Predicate: check if there exists a consecutive pair in the array
-- A consecutive pair is when a[i] + 1 = a[i+1] for some valid index i
def hasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!

-- Postcondition clause
def ensures1 (a : Array Int) (result : Bool) :=
  result = true ↔ hasConsecutivePair a

def precondition (a : Array Int) :=
  True

-- no preconditions

def postcondition (a : Array Int) (result : Bool) :=
  ensures1 a result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.containsConsecutiveNumbers_precond a ↔ LeetProofSpec.precondition a := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.containsConsecutiveNumbers_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Bool) (h_precond : VerinaSpec.containsConsecutiveNumbers_precond a):
  VerinaSpec.containsConsecutiveNumbers_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- Since the conditions for the existence of consecutive pairs are equivalent, we can conclude that the postconditions are equivalent.
  apply Iff.intro;
  · intro h;
    cases result <;> simp_all +decide [ LeetProofSpec.postcondition ];
    · unfold VerinaSpec.containsConsecutiveNumbers_postcond at h;
      simp_all +decide [ LeetProofSpec.ensures1 ];
      exact fun ⟨ i, hi, hi' ⟩ => h i ( Nat.lt_pred_iff.mpr hi ) hi';
    · simp_all +decide [ LeetProofSpec.ensures1, VerinaSpec.containsConsecutiveNumbers_postcond ];
      exact ⟨ h.choose, Nat.lt_pred_iff.mp h.choose_spec.1, h.choose_spec.2 ⟩;
  · -- Since the conditions for the existence of consecutive pairs are equivalent, we can conclude that the postconditions are equivalent. Therefore, the implication holds.
    intro h_postcond
    simp [VerinaSpec.containsConsecutiveNumbers_postcond, LeetProofSpec.postcondition] at *;
    cases result <;> simp_all +decide [ LeetProofSpec.ensures1 ];
    · -- By definition of `hasConsecutivePair`, if there are no consecutive pairs, then for any `x < a.size - 1`, `a[x]! + 1 ≠ a[x + 1]!`.
      intros x hx
      by_contra h_contra
      exact h_postcond ⟨x, by
        exact Nat.lt_pred_iff.mp hx, h_contra⟩;
    · obtain ⟨ i, hi ⟩ := h_postcond;
      exact ⟨ i, Nat.lt_pred_iff.mpr hi.1, hi.2 ⟩