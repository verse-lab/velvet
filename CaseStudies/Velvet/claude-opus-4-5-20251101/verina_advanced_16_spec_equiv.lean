/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e93fec80-07d4-40a7-9434-b52770ba4dc6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int):
  VerinaSpec.insertionSort_precond xs ↔ LeetProofSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : List Int) (h_precond : VerinaSpec.insertionSort_precond xs):
  VerinaSpec.insertionSort_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def insertionSort_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def insertionSort_postcond (xs : List Int) (result: List Int) (h_precond : insertionSort_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result ∧ List.isPerm xs result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to check if a list is sorted in ascending order
-- Using List.Sorted from Mathlib with (· ≤ ·) relation
def isSortedAsc (xs : List Int) : Prop :=
  List.Sorted (· ≤ ·) xs

-- Helper function to check if two lists are permutations of each other
-- Using List.Perm from Mathlib (explicit form instead of ~ notation)
def isPermOf (xs : List Int) (ys : List Int) : Prop :=
  List.Perm xs ys

-- Precondition: no constraints on input
def precondition (xs : List Int) : Prop :=
  True

-- Postcondition: result is sorted and is a permutation of input
def postcondition (xs : List Int) (result : List Int) : Prop :=
  isSortedAsc result ∧ isPermOf result xs

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (xs : List Int):
  VerinaSpec.insertionSort_precond xs ↔ LeetProofSpec.precondition xs := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.insertionSort_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (xs : List Int) (result : List Int) (h_precond : VerinaSpec.insertionSort_precond xs):
  VerinaSpec.insertionSort_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result := by
  -- By definition of postcondition in both contexts, we can show that they are equivalent.
  simp [VerinaSpec.insertionSort_postcond, LeetProofSpec.postcondition];
  simp [LeetProofSpec.isSortedAsc, LeetProofSpec.isPermOf];
  -- The pairwise condition for the sorted list is equivalent to the list being sorted.
  simp [List.Sorted];
  simp +decide [ List.perm_iff_count ];
  -- The permutation of two lists is equivalent to the equality of their counts for all elements.
  have h_perm_count : ∀ (xs result : List ℤ), List.isPerm xs result ↔ ∀ a, List.count a xs = List.count a result := by
    intros xs result; exact (by
    -- By definition of permutation, we know that two lists are permutations of each other if and only if they have the same count for every element.
    have h_perm_count : ∀ (xs result : List ℤ), List.Perm xs result ↔ ∀ a, List.count a xs = List.count a result := by
      exact?;
    convert h_perm_count xs result using 1;
    exact?);
  exact fun _ => Iff.trans ( h_perm_count _ _ ) ( forall_congr' fun _ => eq_comm )