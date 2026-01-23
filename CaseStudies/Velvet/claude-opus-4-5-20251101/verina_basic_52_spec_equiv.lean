/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 59ddda29-db18-4d5a-95dd-3cc13fdcab9d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.BubbleSort_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.BubbleSort_precond a):
  VerinaSpec.BubbleSort_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def BubbleSort_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def swap (a : Array Int) (i j : Nat) : Array Int :=
  let temp := a[i]!
  let a₁ := a.set! i (a[j]!)
  a₁.set! j temp

def bubbleInner (j i : Nat) (a : Array Int) : Array Int :=
  if j < i then
    let a' := if a[j]! > a[j+1]! then swap a j (j+1) else a
    bubbleInner (j+1) i a'
  else
    a

def bubbleOuter (i : Nat) (a : Array Int) : Array Int :=
  if i > 0 then
    let a' := bubbleInner 0 i a
    bubbleOuter (i - 1) a'
  else
    a

def BubbleSort_postcond (a : Array Int) (result: Array Int) (h_precond : BubbleSort_precond (a)) :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm result.toList a.toList

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function: check if array is sorted in non-decreasing order
def isSortedArray (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper function: check if two arrays are permutations of each other
-- Using List.Perm via toList
def isPermutationArray (arr1 arr2 : Array Int) : Prop :=
  arr1.toList.Perm arr2.toList

-- Precondition: no restrictions on input array
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition clauses
-- 1. Result is sorted in non-decreasing order
def ensures1 (a : Array Int) (result : Array Int) : Prop :=
  isSortedArray result

-- 2. Result is a permutation of input (preserves multiset and implies same size)
def ensures2 (a : Array Int) (result : Array Int) : Prop :=
  isPermutationArray a result

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  ensures1 a result ∧
  ensures2 a result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.BubbleSort_precond a ↔ LeetProofSpec.precondition a := by
  exact Iff.rfl

theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.BubbleSort_precond a):
  VerinaSpec.BubbleSort_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- Since a sorted list is pairwise non-decreasing, we have `List.Pairwise (· ≤ ·) result.toList ↔ VerinaSpec.BubbleSort_postcond a result h_precond`.
  apply Iff.intro;
  · -- If the result is a permutation of the input and is sorted, then it's a permutation of the input and is sorted.
    intro h_postcond
    obtain ⟨h_sorted, h_perm⟩ := h_postcond
    exact ⟨by
    intro i j hij hj;
    rw [ List.pairwise_iff_get ] at h_sorted;
    convert h_sorted ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij;
    · grind;
    · grind, by
      apply List.Perm.symm;
      exact?⟩;
  · intro h;
    constructor;
    · -- By definition of `isSortedArray`, if `result` is sorted, then for any `i < j`, `result[i]! ≤ result[j]!`.
      have h_sorted : ∀ i j : Nat, i < j → j < result.size → result[i]! ≤ result[j]! := by
        exact h.1;
      rw [ List.pairwise_iff_get ];
      -- Since the list is just the array's elements, the indices are the same. Therefore, the inequality holds for the list elements as well.
      intros i j hij
      have h_ij : i.val < j.val := by
        exact?;
      grind;
    · -- Since `isPermutationArray` is defined as `List.Perm`, we can directly use `h.2` to conclude the proof.
      convert h.2.symm using 1;
      exact?