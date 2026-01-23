/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0f118538-33f5-430b-bd80-e61af9fd3b3a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.SelectionSort_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.SelectionSort_precond a):
  VerinaSpec.SelectionSort_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def SelectionSort_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a

def SelectionSort_postcond (a : Array Int) (result: Array Int) (h_precond : SelectionSort_precond (a)) :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm a.toList result.toList

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: Check if two arrays are permutations of each other using count equality
def isPermutation (a b : Array Int) : Prop :=
  a.size = b.size ∧ ∀ x : Int, a.toList.count x = b.toList.count x

-- Precondition: no constraints needed, any array is valid input
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is sorted and is a permutation of input
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  isSortedNonDecreasing result ∧ isPermutation a result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.SelectionSort_precond a ↔ LeetProofSpec.precondition a := by
  -- Since both preconditions are true, the equivalence holds trivially.
  simp [VerinaSpec.SelectionSort_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.SelectionSort_precond a):
  VerinaSpec.SelectionSort_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  constructor <;> intro h;
  · -- By definition of `VerinaSpec.SelectionSort_postcond`, we know that `result` is a permutation of `a` and is sorted in non-decreasing order.
    obtain ⟨h_perm, h_sorted⟩ := h;
    -- Since the result is pairwise sorted, it is already sorted in non-decreasing order.
    have h_sorted_nondec : LeetProofSpec.isSortedNonDecreasing result := by
      intro i j hij hj;
      have := List.pairwise_iff_get.mp h_perm;
      convert this ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij;
      · grind;
      · grind;
    -- Since the result is a permutation of the original array and is sorted, we can conclude the proof.
    apply And.intro h_sorted_nondec;
    -- Since the lists are permutations, their counts are equal.
    have h_count_eq : ∀ x : Int, a.toList.count x = result.toList.count x := by
      -- Since the lists are permutations of each other, the count of any element in both lists is equal.
      intros x
      apply List.Perm.count_eq;
      exact?;
    -- Since the counts are equal, the lists are permutations of each other.
    have h_perm : List.Perm a.toList result.toList := by
      exact?;
    exact ⟨ by simpa using h_perm.length_eq, h_count_eq ⟩;
  · constructor;
    · have := h.1;
      rw [ List.pairwise_iff_get ];
      intro i j hij; have := this i j; aesop;
    · have h_perm : a.toList.Perm result.toList := by
        -- Since the counts of all elements are equal, the lists are permutations.
        have h_perm : ∀ x : ℤ, a.toList.count x = result.toList.count x := by
          exact h.2.2;
        grind;
      exact?