/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 97f9a76c-1d83-4190-96b6-f48524e2ec07

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (l : List Int):
  VerinaSpec.insertionSort_precond l ↔ LeetProofSpec.precondition l

- theorem postcondition_equiv (l : List Int) (result : List Int) (h_precond : VerinaSpec.insertionSort_precond l):
  VerinaSpec.insertionSort_postcond l result h_precond ↔ LeetProofSpec.postcondition l result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def insertionSort_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

-- Helper function to insert an integer into a sorted list
def insertElement (x : Int) (l : List Int) : List Int :=
  match l with
  | [] => [x]
  | y :: ys =>
      if x <= y then
        x :: y :: ys
      else
        y :: insertElement x ys

-- Helper function to sort a list using insertion sort
def sortList (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs =>
      insertElement x (sortList xs)

@[reducible]
def insertionSort_postcond (l : List Int) (result: List Int) (h_precond : insertionSort_precond (l)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result ∧ List.isPerm l result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input list
def precondition (l : List Int) : Prop :=
  True

-- Postcondition: Result is sorted and is a permutation of input
-- Using Mathlib's List.Sorted for sortedness property
-- Using List.Perm for permutation property
def postcondition (l : List Int) (result : List Int) : Prop :=
  List.Sorted (· ≤ ·) result ∧ List.Perm l result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (l : List Int):
  VerinaSpec.insertionSort_precond l ↔ LeetProofSpec.precondition l := by
  exact iff_of_true trivial trivial

theorem postcondition_equiv (l : List Int) (result : List Int) (h_precond : VerinaSpec.insertionSort_precond l):
  VerinaSpec.insertionSort_postcond l result h_precond ↔ LeetProofSpec.postcondition l result := by
  unfold VerinaSpec.insertionSort_postcond LeetProofSpec.postcondition;
  -- The pairwise condition for sortedness is equivalent to the sortedness condition in Lean.
  simp [List.Sorted];
  -- The permutation relation is reflexive, so if l is a permutation of result, then result is also a permutation of l.
  simp [List.isPerm_iff]