/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 258a7dff-ff6a-46ac-a130-07c8ce642497

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Nat):
  VerinaSpec.majorityElement_precond xs ↔ LeetProofSpec.precondition xs

- theorem postcondition_equiv (xs : List Nat) (result : Nat) (h_precond : VerinaSpec.majorityElement_precond xs):
  VerinaSpec.majorityElement_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def majorityElement_precond (xs : List Nat) : Prop :=
  -- !benchmark @start precond
  xs.length > 0 ∧ xs.any (fun x => xs.count x > xs.length / 2)

-- !benchmark @end precond

@[reducible]
def majorityElement_postcond (xs : List Nat) (result: Nat) (h_precond : majorityElement_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  let count := xs.count result
  count > xs.length / 2

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: list is non-empty and contains a majority element
def precondition (xs : List Nat) :=
  xs.length > 0 ∧ ∃ x ∈ xs, xs.count x > xs.length / 2

-- Postcondition: result is in the list and appears more than half the time
def postcondition (xs : List Nat) (result : Nat) :=
  result ∈ xs ∧ xs.count result > xs.length / 2

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (xs : List Nat):
  VerinaSpec.majorityElement_precond xs ↔ LeetProofSpec.precondition xs := by
  -- The two preconditions are equivalent because they both require the list to be non-empty and have a majority element.
  simp [VerinaSpec.majorityElement_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (xs : List Nat) (result : Nat) (h_precond : VerinaSpec.majorityElement_precond xs):
  VerinaSpec.majorityElement_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result := by
  -- The postconditions are equivalent because if the count is greater than half the length, then the element must be in the list.
  simp [VerinaSpec.majorityElement_postcond, LeetProofSpec.postcondition];
  -- If the count of `result` in `xs` is greater than half the length of `xs`, then `result` must be in `xs`.
  intro h_count
  by_contra h_not_in
  have h_count_zero : List.count result xs = 0 := by
    -- If `result` is not in `xs`, then by definition of `List.count`, the count of `result` in `xs` is zero.
    apply List.count_eq_zero_of_not_mem; assumption;
  grind