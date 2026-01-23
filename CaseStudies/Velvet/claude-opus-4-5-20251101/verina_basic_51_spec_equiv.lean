/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 44e42d76-0c9e-4f97-a568-0540be463ba8

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (key : Int):
  VerinaSpec.BinarySearch_precond a key ↔ LeetProofSpec.precondition a key

- theorem postcondition_equiv (a : Array Int) (key : Int) (result : Nat) (h_precond : VerinaSpec.BinarySearch_precond a key):
  VerinaSpec.BinarySearch_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def BinarySearch_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a.toList

-- !benchmark @end precond

def binarySearchLoop (a : Array Int) (key : Int) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if (a[mid]! < key) then binarySearchLoop a key (mid + 1) hi
    else binarySearchLoop a key lo mid
  else
    lo

def BinarySearch_postcond (a : Array Int) (key : Int) (result: Nat) (h_precond : BinarySearch_precond (a) (key)) :=
  -- !benchmark @start postcond
  result ≤ a.size ∧
  ((a.take result).all (fun x => x < key)) ∧
  ((a.drop result).all (fun x => x ≥ key))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper definition: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition: array must be sorted in non-decreasing order
def precondition (a : Array Int) (key : Int) : Prop :=
  isSortedNonDecreasing a

-- Postcondition clauses
-- 1. Result is a valid index (between 0 and size inclusive)
def ensures1 (a : Array Int) (key : Int) (result : Nat) : Prop :=
  result ≤ a.size

-- 2. All elements before the result index are strictly less than the key
def ensures2 (a : Array Int) (key : Int) (result : Nat) : Prop :=
  ∀ i : Nat, i < result → a[i]! < key

-- 3. All elements from the result index onwards are greater than or equal to the key
def ensures3 (a : Array Int) (key : Int) (result : Nat) : Prop :=
  ∀ i : Nat, result ≤ i → i < a.size → a[i]! ≥ key

def postcondition (a : Array Int) (key : Int) (result : Nat) : Prop :=
  ensures1 a key result ∧
  ensures2 a key result ∧
  ensures3 a key result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (key : Int):
  VerinaSpec.BinarySearch_precond a key ↔ LeetProofSpec.precondition a key := by
  constructor;
  · intro h i j hij hj;
    have := List.pairwise_iff_get.mp h;
    convert this ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij;
    · grind;
    · grind;
  · intro h_sorted
    apply List.pairwise_iff_get.mpr;
    intro i j hij; specialize h_sorted i j hij; aesop;

theorem postcondition_equiv (a : Array Int) (key : Int) (result : Nat) (h_precond : VerinaSpec.BinarySearch_precond a key):
  VerinaSpec.BinarySearch_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result := by
  -- To prove the equivalence, we show that the conditions on the take and drop of the array are equivalent to the conditions on the elements before and after the result index.
  apply Iff.intro;
  · -- By definition of `postcondition`, we need to show that `result ≤ a.size`, `∀ i < result, a[i]! < key`, and `∀ i ≥ result, i < a.size → a[i]! ≥ key`.
    intro h
    obtain ⟨h1, h2, h3⟩ := h;
    refine' ⟨ h1, _, _ ⟩;
    · intro i hi; have := h2; simp_all +decide [ Array.all_eq ] ;
      rw [ Array.all_iff_forall ] at h2;
      grind;
    · intro i hi₁ hi₂;
      rw [ Array.all_eq_true ] at h3;
      specialize h3 ( i - result ) ; simp_all +decide [ Nat.sub_add_cancel hi₁ ];
      exact h3 ( by omega );
  · intro h_post;
    refine' ⟨ h_post.1, _, _ ⟩;
    · -- By definition of `h_post`, we know that for all `i < result`, `a[i]! < key`.
      have h_take : ∀ i < result, a[i]! < key := by
        exact h_post.2.1;
      rw [ Array.all_eq_true ];
      norm_num +zetaDelta at *;
      exact fun i hi₁ hi₂ => by simpa [ hi₂ ] using h_take i hi₁;
    · -- By definition of postcondition, we know that all elements from result onwards are greater than or equal to the key.
      have h_drop : ∀ i : ℕ, result ≤ i → i < a.size → a[i]! ≥ key := by
        exact h_post.2.2;
      -- By definition of `drop`, every element in the drop is at an index i such that result ≤ i.
      have h_drop_indices : ∀ i : ℕ, i < (a.drop result).size → (a.drop result)[i]! = a[result + i]! := by
        grind;
      grind