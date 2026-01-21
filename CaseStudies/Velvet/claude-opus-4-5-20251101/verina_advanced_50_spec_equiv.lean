/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9caa271c-3957-4ed9-8e21-901d53dc547d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a1 : Array Nat) (a2 : Array Nat):
  VerinaSpec.mergeSorted_precond a1 a2 ↔ LeetProofSpec.precondition a1 a2

- theorem postcondition_equiv (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) (h_precond : VerinaSpec.mergeSorted_precond a1 a2):
  VerinaSpec.mergeSorted_postcond a1 a2 result h_precond ↔ LeetProofSpec.postcondition a1 a2 result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def mergeSorted_precond (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a1.toList ∧ List.Pairwise (· ≤ ·) a2.toList

-- !benchmark @end precond

@[reducible]
def mergeSorted_postcond (a1 : Array Nat) (a2 : Array Nat) (result: Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧
  result.toList.isPerm (a1.toList ++ a2.toList)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: check if an array is sorted in non-decreasing order
def isSortedArray (arr : Array Nat) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: count occurrences of a value in an array
def countInArray (arr : Array Nat) (v : Nat) : Nat :=
  arr.toList.count v

-- Precondition: both input arrays must be sorted
def precondition (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  isSortedArray a1 ∧ isSortedArray a2

-- Postcondition clauses
-- 1. The result size equals the sum of input sizes
def ensures1 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  result.size = a1.size + a2.size

-- 2. The result is sorted in non-decreasing order
def ensures2 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  isSortedArray result

-- 3. Every element's count in result equals its count in a1 plus its count in a2
def ensures3 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  ∀ v : Nat, countInArray result v = countInArray a1 v + countInArray a2 v

def postcondition (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  ensures1 a1 a2 result ∧
  ensures2 a1 a2 result ∧
  ensures3 a1 a2 result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a1 : Array Nat) (a2 : Array Nat):
  VerinaSpec.mergeSorted_precond a1 a2 ↔ LeetProofSpec.precondition a1 a2 := by
  constructor;
  · intro h_precond
    obtain ⟨h1, h2⟩ := h_precond;
    refine' ⟨ _, _ ⟩ <;> simp_all +decide [ List.pairwise_iff_get ];
    · intro i j hij hj; convert h1 ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij using 1;
      · exact?;
      · exact?;
    · intro i j hij hj; convert h2 ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij using 1;
      · exact?;
      · exact?;
  · -- If the arrays are sorted, then their toList versions are also sorted.
    intro h_precond
    obtain ⟨h_a1, h_a2⟩ := h_precond;
    refine' ⟨ _, _ ⟩;
    · refine' List.pairwise_iff_get.mpr _;
      intro i j hij; have := h_a1 i j hij; aesop;
    · rw [ List.pairwise_iff_get ];
      intro i j hij; have := h_a2 i j hij; aesop;

theorem postcondition_equiv (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) (h_precond : VerinaSpec.mergeSorted_precond a1 a2):
  VerinaSpec.mergeSorted_postcond a1 a2 result h_precond ↔ LeetProofSpec.postcondition a1 a2 result := by
  constructor <;> intro h;
  · -- By definition of `mergeSorted_postcond`, we know that `result.toList` is sorted and is a permutation of `a1.toList ++ a2.toList`.
    obtain ⟨h_sorted, h_perm⟩ := h;
    refine' ⟨ _, _, _ ⟩;
    · -- Since `result.toList` is a permutation of `a1.toList ++ a2.toList`, their lengths must be equal.
      have h_length : result.toList.length = (a1.toList ++ a2.toList).length := by
        -- Since permutations preserve length, we can conclude that the lengths of `result.toList` and `a1.toList ++ a2.toList` are equal.
        apply List.Perm.length_eq;
        exact?;
      aesop;
    · intro i j hij hj;
      have := List.pairwise_iff_get.mp h_sorted;
      simp +zetaDelta at *;
      convert this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij;
      · exact?;
      · exact?;
    · -- Since the result is a permutation of the concatenation of a1 and a2, the count of any element v in the result is equal to the sum of the counts in a1 and a2.
      have h_count : ∀ v : ℕ, List.count v result.toList = List.count v (a1.toList ++ a2.toList) := by
        -- Since the lists are permutations, their counts for any element are equal. Therefore, for any v, List.count v result.toList = List.count v (a1.toList ++ a2.toList).
        intros v
        apply List.Perm.count_eq (by
        exact?);
      exact fun v => by simpa [ LeetProofSpec.countInArray ] using h_count v;
  · -- By combining the results from the postcondition, we can conclude that the result is sorted and a permutation of the concatenation.
    apply And.intro;
    · have := h.2.1;
      -- By definition of `isSortedArray`, we know that for any `i < j`, `result[i] ≤ result[j]`.
      have h_sorted : ∀ i j : ℕ, i < j → j < result.size → result[i]! ≤ result[j]! := by
        exact this;
      -- By definition of `List.Pairwise`, we need to show that for any `i < j`, `result[i]! ≤ result[j]!`.
      have h_pairwise : ∀ i j : ℕ, i < j → i < result.size → j < result.size → result[i]! ≤ result[j]! := by
        exact fun i j hij hi hj => h_sorted i j hij hj;
      rw [ List.pairwise_iff_get ] ; aesop;
    · -- By definition of `countInArray`, we know that `countInArray result v = countInArray a1 v + countInArray a2 v` for all `v`.
      have h_count : ∀ v, List.count v (result.toList) = List.count v (a1.toList) + List.count v (a2.toList) := by
        convert h.2.2;
      -- By definition of permutation, if two lists have the same count for every element, then they are permutations of each other.
      have h_perm : List.Perm result.toList (a1.toList ++ a2.toList) := by
        rw [ List.perm_iff_count ];
        simp_all +decide [ Array.count ];
      exact?