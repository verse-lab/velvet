/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 83c56942-fb52-4413-91c5-b30edddc7a09

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.swapFirstAndLast_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.swapFirstAndLast_precond a):
  VerinaSpec.swapFirstAndLast_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def swapFirstAndLast_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0

-- !benchmark @end precond

def swapFirstAndLast_postcond (a : Array Int) (result : Array Int) (h_precond: swapFirstAndLast_precond a) : Prop :=
  -- !benchmark @start postcond
  result.size = a.size ∧
  result[0]! = a[a.size - 1]! ∧
  result[result.size - 1]! = a[0]! ∧
  (List.range (result.size - 2)).all (fun i => result[i + 1]! = a[i + 1]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: Array must be non-empty
def precondition (a : Array Int) : Prop :=
  a.size ≥ 1

-- Postcondition: Describes the swapped array properties
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  -- Same size as input
  result.size = a.size ∧
  -- First element of result is last element of input
  result[0]! = a[a.size - 1]! ∧
  -- Last element of result is first element of input
  result[result.size - 1]! = a[0]! ∧
  -- All middle elements remain unchanged
  (∀ i : Nat, 0 < i → i < a.size - 1 → result[i]! = a[i]!)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.swapFirstAndLast_precond a ↔ LeetProofSpec.precondition a := by
  bound

theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.swapFirstAndLast_precond a):
  VerinaSpec.swapFirstAndLast_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- By definition of `swapFirstAndLast_postcond` and `LeetProofSpec.postcondition`, we can show that they are equivalent by comparing their conditions.
  simp [VerinaSpec.swapFirstAndLast_postcond, LeetProofSpec.postcondition];
  -- Since the range in `List.range (result.size - 2)` is equivalent to the range in the LeetPostcondition's `∀ i` statement, the two conditions are equivalent.
  intros h_size h_first h_last
  apply Iff.intro;
  · -- By substituting $x = i - 1$ into the hypothesis, we can conclude that $result[i]! = a[i]!$ for all $i$ in the specified range.
    intros h x hx_pos hx_lt
    have hx_range : x - 1 < result.size - 2 := by
      omega;
    cases x <;> aesop;
  · grind