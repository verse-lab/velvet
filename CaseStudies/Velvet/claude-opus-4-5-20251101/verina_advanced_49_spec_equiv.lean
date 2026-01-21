/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ecd1f394-ac59-45fb-986f-0f6761f81703

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr1 : List Int) (arr2 : List Int):
  VerinaSpec.mergeSortedLists_precond arr1 arr2 ↔ LeetProofSpec.precondition arr1 arr2

- theorem postcondition_equiv (arr1 : List Int) (arr2 : List Int) (result : List Int) (h_precond : VerinaSpec.mergeSortedLists_precond arr1 arr2):
  VerinaSpec.mergeSortedLists_postcond arr1 arr2 result h_precond ↔ LeetProofSpec.postcondition arr1 arr2 result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def mergeSortedLists_precond (arr1 : List Int) (arr2 : List Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr1 ∧ List.Pairwise (· ≤ ·) arr2

-- !benchmark @end precond

@[reducible]
def mergeSortedLists_postcond (arr1 : List Int) (arr2 : List Int) (result: List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result ∧ List.isPerm (arr1 ++ arr2) result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper to check if a list is sorted in ascending order (using ≤)
def isSortedAsc (lst : List Int) : Prop :=
  List.Sorted (· ≤ ·) lst

-- Helper to count occurrences of an element in a list
def countOccurrences (x : Int) (lst : List Int) : Nat :=
  lst.filter (· == x) |>.length

-- Precondition: both input lists must be sorted in ascending order
def precondition (arr1 : List Int) (arr2 : List Int) : Prop :=
  isSortedAsc arr1 ∧ isSortedAsc arr2

-- Postcondition clauses
-- 1. The result is sorted in ascending order
def ensures1 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  isSortedAsc result

-- 2. The result has the correct length (all elements preserved)
def ensures2 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  result.length = arr1.length + arr2.length

-- 3. Every element in result comes from arr1 or arr2
def ensures3 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  ∀ x, x ∈ result → x ∈ arr1 ∨ x ∈ arr2

-- 4. Every element from arr1 and arr2 is in result (with correct multiplicity)
def ensures4 (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  ∀ x, countOccurrences x result = countOccurrences x arr1 + countOccurrences x arr2

def postcondition (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  ensures1 arr1 arr2 result ∧
  ensures2 arr1 arr2 result ∧
  ensures3 arr1 arr2 result ∧
  ensures4 arr1 arr2 result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr1 : List Int) (arr2 : List Int):
  VerinaSpec.mergeSortedLists_precond arr1 arr2 ↔ LeetProofSpec.precondition arr1 arr2 := by
  rfl

theorem postcondition_equiv (arr1 : List Int) (arr2 : List Int) (result : List Int) (h_precond : VerinaSpec.mergeSortedLists_precond arr1 arr2):
  VerinaSpec.mergeSortedLists_postcond arr1 arr2 result h_precond ↔ LeetProofSpec.postcondition arr1 arr2 result := by
  -- By definition of `mergeSortedLists_postcond` and `postcondition`, we need to show that the results are permutations and have the same length.
  apply Iff.intro;
  · -- By definition of `mergeSortedLists_postcond`, if `result` is a permutation of `arr1 ++ arr2` and is sorted, then it satisfies all the postcondition clauses.
    intro h_post
    obtain ⟨h_perm, h_sorted⟩ := h_post;
    -- By definition of `List.isPerm`, we know that `arr1 ++ arr2` and `result` have the same elements with the same multiplicities.
    have h_perm_eq : ∀ x, List.count x (arr1 ++ arr2) = List.count x result := by
      intro x; have := List.Perm.count_eq ( show List.Perm ( arr1 ++ arr2 ) result from by rw [ List.isPerm_iff ] at h_sorted; aesop ) x; aesop;
    refine' ⟨ _, _, _, _ ⟩;
    · exact?;
    · convert List.Perm.length_eq ( show List.Perm ( arr1 ++ arr2 ) result from ?_ ) using 1;
      · unfold LeetProofSpec.ensures2; aesop;
      · grind;
    · intro x hx; specialize h_perm_eq x; contrapose! h_perm_eq; simp_all +decide [ List.count_eq_zero_of_not_mem ] ;
      exact ne_of_lt ( List.count_pos_iff.mpr hx );
    · intro x; specialize h_perm_eq x; simp_all +decide [ LeetProofSpec.countOccurrences ] ;
      grind;
  · -- If result is a permutation of arr1 ++ arr2 and the counts are preserved, then it's sorted and the permutation condition holds.
    intro h_postcond
    have h_sorted : List.Pairwise (· ≤ ·) result := by
      exact h_postcond.1
    have h_perm : List.isPerm (arr1 ++ arr2) result := by
      -- By definition of `postcondition`, we know that `result` is a permutation of `arr1 ++ arr2`.
      have h_perm : List.Perm (arr1 ++ arr2) result := by
        -- By definition of `postcondition`, we know that `result` is a permutation of `arr1 ++ arr2` because they have the same length and the same counts for all elements.
        apply List.perm_iff_count.mpr;
        intro x; have := h_postcond.2.2.2 x; simp_all +decide [ List.count ] ;
        convert this.symm using 1 <;> simp +decide [ List.countP_eq_length_filter ];
        · rfl;
        · exact?;
      exact?
    exact ⟨h_sorted, h_perm⟩