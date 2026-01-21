/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d2a98433-65f6-4e79-afe0-724304c00f17

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.removeDuplicates_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Nat) (h_precond : VerinaSpec.removeDuplicates_precond nums):
  VerinaSpec.removeDuplicates_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def removeDuplicates_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  -- nums are sorted in non-decreasing order
  List.Pairwise (· ≤ ·) nums

-- !benchmark @end precond

@[reducible]
def removeDuplicates_postcond (nums : List Int) (result: Nat) (h_precond : removeDuplicates_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  result - nums.eraseDups.length = 0 ∧
  nums.eraseDups.length ≤ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if list is sorted in non-decreasing order
def isSortedNonDecreasing (nums : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < nums.length → nums[i]! ≤ nums[j]!

-- Precondition: The input list must be sorted in non-decreasing order
def precondition (nums : List Int) : Prop :=
  isSortedNonDecreasing nums

-- Postcondition: The result is the count of unique elements
-- Using Finset.card which gives the cardinality of the set of distinct elements
-- This is a declarative specification that describes what "unique count" means
-- without encoding a specific algorithm for computing it
def postcondition (nums : List Int) (result : Nat) : Prop :=
  result = nums.toFinset.card

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.removeDuplicates_precond nums ↔ LeetProofSpec.precondition nums := by
  -- To prove the equivalence, we show that if the list is pairwise sorted, then for any i < j, the element at i is less than or equal to the element at j, and vice versa.
  apply Iff.intro;
  · intro h_sorted i j hij hj_lt_len
    have h_le : nums[i]! ≤ nums[j]! := by
      have := List.pairwise_iff_get.mp h_sorted;
      convert this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij using 1;
      · grind;
      · grind
    exact h_le;
  · intro h;
    convert List.pairwise_iff_get.mpr _;
    intro i j hij; have := h i j; aesop;

theorem postcondition_equiv (nums : List Int) (result : Nat) (h_precond : VerinaSpec.removeDuplicates_precond nums):
  VerinaSpec.removeDuplicates_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  -- Since the list is sorted, the length of the list after removing duplicates is equal to the cardinality of the Finset of the list.
  have h_sorted_unique : ∀ {xs : List ℤ}, List.Pairwise (· ≤ ·) xs → xs.eraseDups.length = xs.toFinset.card := by
    intros xs hxs
    induction' xs using List.reverseRecOn with xs ih;
    · rfl;
    · by_cases h : ih ∈ xs <;> simp_all +decide [ List.pairwise_append ];
      · simp_all +decide [ List.eraseDups_append ];
        simp_all +decide [ List.removeAll ];
      · simp_all +decide [ List.eraseDups_append ];
        rw [ List.removeAll ] ; aesop;
  -- Apply the hypothesis `h_sorted_unique` to the list `nums` since it is pairwise sorted.
  have h_eq : nums.eraseDups.length = nums.toFinset.card := by
    exact h_sorted_unique h_precond;
  -- By combining the results from h_eq and the definitions of the postconditions, we can conclude the equivalence.
  simp [h_eq, VerinaSpec.removeDuplicates_postcond, LeetProofSpec.postcondition];
  exact ⟨ fun h => by omega, fun h => by omega ⟩