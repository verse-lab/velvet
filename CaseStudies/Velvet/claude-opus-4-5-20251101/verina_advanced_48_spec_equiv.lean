/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 09060d12-8319-4dd5-86ae-c12e3b42faa0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (list : List Int):
  VerinaSpec.mergeSort_precond list ↔ LeetProofSpec.precondition list

- theorem postcondition_equiv (list : List Int) (result : List Int) (h_precond : VerinaSpec.mergeSort_precond list):
  VerinaSpec.mergeSort_postcond list result h_precond ↔ LeetProofSpec.postcondition list result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def mergeSort_precond (list : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def mergeSort_postcond (list : List Int) (result: List Int) (h_precond : mergeSort_precond (list)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result ∧ List.isPerm list result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function: check if a list is sorted in ascending order (non-strict)
def isSortedAsc (l : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < l.length → l[i]! ≤ l[j]!

-- Helper function: check if two lists are permutations of each other
-- Using List.Perm from Mathlib which captures that two lists have the same elements with same multiplicities
def isPermutation (l1 l2 : List Int) : Prop :=
  List.Perm l1 l2

-- Precondition: no restrictions on input
def precondition (list : List Int) : Prop :=
  True

-- Postcondition: result is sorted and is a permutation of input
def postcondition (list : List Int) (result : List Int) : Prop :=
  isSortedAsc result ∧ isPermutation list result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (list : List Int):
  VerinaSpec.mergeSort_precond list ↔ LeetProofSpec.precondition list := by
  -- Since both preconditions are True, they are trivially equivalent.
  simp [VerinaSpec.mergeSort_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (list : List Int) (result : List Int) (h_precond : VerinaSpec.mergeSort_precond list):
  VerinaSpec.mergeSort_postcond list result h_precond ↔ LeetProofSpec.postcondition list result := by
  unfold LeetProofSpec.postcondition;
  -- By definition of pairwise sortedness, we know that `List.Pairwise (· ≤ ·) result` is equivalent to `LeetProofSpec.isSortedAsc result`.
  have h_pairwise_sorted : List.Pairwise (· ≤ ·) result ↔ LeetProofSpec.isSortedAsc result := by
    -- The pairwise condition is equivalent to the isSortedAsc condition because if the list is pairwise sorted, then for any i < j, the element at i is less than or equal to the element at j, which is exactly what isSortedAsc states. Conversely, if the list is sorted in non-decreasing order, then every pair of consecutive elements must satisfy the pairwise condition.
    apply Iff.intro;
    · intro h_pairwise_sorted i j hij hlt
      have h_le : result[i]! ≤ result[j]! := by
        have := List.pairwise_iff_get.mp h_pairwise_sorted;
        -- Since $i < j$ and both are within the bounds of the list, we can apply the pairwise condition to get the desired inequality.
        have h_pairwise : result.get ⟨i, by linarith⟩ ≤ result.get ⟨j, by linarith⟩ := by
          exact this _ _ hij;
        grind
      exact h_le;
    · intro h_sorted;
      rw [ List.pairwise_iff_get ];
      -- By definition of isSortedAsc, for any i < j, result[i]! ≤ result[j]!.
      intros i j hij
      have := h_sorted i j hij
      aesop;
  -- Apply the equivalence from h_pairwise_sorted to conclude the proof.
  simp [h_pairwise_sorted, VerinaSpec.mergeSort_postcond, LeetProofSpec.isPermutation];
  exact?