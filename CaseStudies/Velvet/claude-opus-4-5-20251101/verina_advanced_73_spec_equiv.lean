/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 39ca6adc-6df9-4078-918d-83314d37a347

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (l : List Nat):
  VerinaSpec.smallestMissing_precond l ↔ LeetProofSpec.precondition l

- theorem postcondition_equiv (l : List Nat) (result : Nat) (h_precond : VerinaSpec.smallestMissing_precond l):
  VerinaSpec.smallestMissing_postcond l result h_precond ↔ LeetProofSpec.postcondition l result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def smallestMissing_precond (l : List Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· < ·) l

-- !benchmark @end precond

@[reducible]
def smallestMissing_postcond (l : List Nat) (result: Nat) (h_precond : smallestMissing_precond (l)) : Prop :=
  -- !benchmark @start postcond
  result ∉ l ∧ ∀ candidate : Nat, candidate < result → candidate ∈ l

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper definition: check if list is sorted in strictly increasing order
def isStrictlySorted (l : List Nat) : Prop :=
  ∀ i j : Nat, i < j → j < l.length → l[i]! < l[j]!

-- Precondition: list must be sorted in strictly increasing order
def precondition (l : List Nat) : Prop :=
  isStrictlySorted l

-- Postcondition clauses
-- 1. The result is not in the list
def ensures1 (l : List Nat) (result : Nat) : Prop :=
  result ∉ l

-- 2. All natural numbers less than result are in the list
def ensures2 (l : List Nat) (result : Nat) : Prop :=
  ∀ k : Nat, k < result → k ∈ l

def postcondition (l : List Nat) (result : Nat) : Prop :=
  ensures1 l result ∧ ensures2 l result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (l : List Nat):
  VerinaSpec.smallestMissing_precond l ↔ LeetProofSpec.precondition l := by
  -- The pairwise condition in VerinaSpec is equivalent to the isStrictlySorted condition in LeetProofSpec.
  simp [VerinaSpec.smallestMissing_precond, LeetProofSpec.precondition];
  unfold LeetProofSpec.isStrictlySorted;
  constructor;
  · intro h i j hij hj;
    have := List.pairwise_iff_get.mp h;
    convert this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij;
    · grind;
    · grind;
  · rw [ List.pairwise_iff_get ];
    -- Since Fin l.length is a subtype of ℕ, we can convert the indices to natural numbers and apply the hypothesis.
    intro h i j hij
    have h_nat : i.val < j.val ∧ j.val < l.length := by
      exact ⟨ hij, j.2 ⟩;
    grind

theorem postcondition_equiv (l : List Nat) (result : Nat) (h_precond : VerinaSpec.smallestMissing_precond l):
  VerinaSpec.smallestMissing_postcond l result h_precond ↔ LeetProofSpec.postcondition l result := by
  exact?