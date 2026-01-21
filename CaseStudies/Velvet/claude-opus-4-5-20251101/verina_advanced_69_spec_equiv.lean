/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e0498311-c472-473f-b91e-bc77fb7d3ea6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int) (target : Int):
  VerinaSpec.searchInsert_precond xs target ↔ LeetProofSpec.precondition xs target

- theorem postcondition_equiv (xs : List Int) (target : Int) (result : Nat) (h_precond : VerinaSpec.searchInsert_precond xs target):
  VerinaSpec.searchInsert_postcond xs target result h_precond ↔ LeetProofSpec.postcondition xs target result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def searchInsert_precond (xs : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· < ·) xs

-- !benchmark @end precond

@[reducible]
def searchInsert_postcond (xs : List Int) (target : Int) (result: Nat) (h_precond : searchInsert_precond (xs) (target)) : Prop :=
  -- !benchmark @start postcond
  let allBeforeLess := (List.range result).all (fun i => xs[i]! < target)
  let inBounds := result ≤ xs.length
  let insertedCorrectly :=
    result < xs.length → target ≤ xs[result]!
  inBounds ∧ allBeforeLess ∧ insertedCorrectly

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a list is sorted in strictly increasing order
def isStrictlyIncreasing (xs : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < xs.length → xs[i]! < xs[j]!

-- Helper: Count elements in list strictly less than a given value
def countLessThan (xs : List Int) (target : Int) : Nat :=
  xs.countP (· < target)

-- Precondition: The list must be sorted in strictly increasing order (implies no duplicates)
def precondition (xs : List Int) (target : Int) : Prop :=
  isStrictlyIncreasing xs

-- Postcondition clauses:
-- 1. Result is in valid range [0, xs.length]
def ensures1 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  result ≤ xs.length

-- 2. All elements before result index are strictly less than target
def ensures2 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  ∀ i : Nat, i < result → i < xs.length → xs[i]! < target

-- 3. All elements from result index onwards are greater than or equal to target
def ensures3 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  ∀ i : Nat, result ≤ i → i < xs.length → xs[i]! ≥ target

-- 4. Result equals the count of elements strictly less than target
def ensures4 (xs : List Int) (target : Int) (result : Nat) : Prop :=
  result = countLessThan xs target

def postcondition (xs : List Int) (target : Int) (result : Nat) : Prop :=
  ensures1 xs target result ∧
  ensures2 xs target result ∧
  ensures3 xs target result ∧
  ensures4 xs target result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (xs : List Int) (target : Int):
  VerinaSpec.searchInsert_precond xs target ↔ LeetProofSpec.precondition xs target := by
  -- The pairwise condition is equivalent to the sortedness condition because if every consecutive pair is strictly increasing, then the entire list is strictly increasing, and vice versa.
  apply Iff.intro (fun h => by
    intro i j hij hj;
    have := List.pairwise_iff_get.mp h;
    convert this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij using 1;
    · grind;
    · grind) (fun h => by
    -- Apply the hypothesis `h` to conclude that the list is pairwise strictly increasing.
    apply List.pairwise_iff_get.mpr;
    exact fun i j hij => h i j hij ( by simp ) |> fun h => by simpa [ List.get ] using h;)

theorem postcondition_equiv (xs : List Int) (target : Int) (result : Nat) (h_precond : VerinaSpec.searchInsert_precond xs target):
  VerinaSpec.searchInsert_postcond xs target result h_precond ↔ LeetProofSpec.postcondition xs target result := by
  constructor <;> intro h;
  · -- By definition of postcondition, we know that result is equal to the count of elements less than the target.
    have h_count : result = List.countP (fun x => x < target) xs := by
      -- By definition of `searchInsert_postcond`, we know that `result` is the index where `target` should be inserted to maintain the sorted order, and all elements before `result` are less than `target`.
      have h_insert_pos : ∀ (i : ℕ), result ≤ i → i < xs.length → target ≤ xs[i]! := by
        -- Since the list is sorted in strictly increasing order, if i is greater than or equal to result, then the element at i must be greater than or equal to target.
        intros i hi hlt
        have h_sorted : ∀ j k, j < k → k < xs.length → xs[j]! < xs[k]! := by
          -- By definition of `searchInsert_precond`, we know that `xs` is pairwise strictly increasing. Therefore, for any `i < j`, `xs[i]! < xs[j]!`.
          intros i j hij hlt
          have h_pairwise : ∀ (i j : ℕ), i < j → j < xs.length → xs[i]! < xs[j]! := by
            intro i j hij hlt
            have h_pairwise : List.Pairwise (· < ·) xs := by
              exact h_precond
            rw [ List.pairwise_iff_get ] at h_pairwise;
            convert h_pairwise ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij using 1;
            · grind;
            · grind;
          exact h_pairwise i j hij hlt;
        grind;
      -- By definition of `countP`, we can split the list into elements less than `target` and elements greater than or equal to `target`.
      have h_split : List.countP (fun x => x < target) xs = List.countP (fun x => x < target) (List.take result xs) + List.countP (fun x => x < target) (List.drop result xs) := by
        rw [ ← List.countP_append, List.take_append_drop ];
      -- Since all elements before `result` are less than `target`, the count of elements less than `target` in the first `result` elements is exactly `result`.
      have h_count_first : List.countP (fun x => x < target) (List.take result xs) = result := by
        have h_count_first : ∀ (i : ℕ), i ≤ result → List.countP (fun x => x < target) (List.take i xs) = i := by
          -- We can prove this by induction on $i$.
          intro i hi
          induction' i with i ih;
          · rfl;
          · rw [ List.take_succ ];
            grind;
        exact h_count_first result le_rfl;
      -- Since all elements from `result` onwards are greater than or equal to `target`, the count of elements less than `target` in the remaining elements is zero.
      have h_count_remaining : List.countP (fun x => x < target) (List.drop result xs) = 0 := by
        rw [ List.countP_eq_zero ];
        intro a ha; rw [ List.mem_iff_get ] at ha; aesop;
      grind;
    -- By definition of postcondition, we know that all elements before the result are less than the target.
    have h_all_before : ∀ i : ℕ, i < result → i < xs.length → xs[i]! < target := by
      grind;
    -- By definition of postcondition, we know that all elements from the result onwards are greater than or equal to the target.
    have h_all_after : ∀ i : ℕ, result ≤ i → i < xs.length → xs[i]! ≥ target := by
      -- Since the list is strictly increasing, for any i ≥ result, xs[i]! ≥ xs[result]!.
      have h_strict_mono : ∀ i j : ℕ, i < j → j < xs.length → xs[i]! < xs[j]! := by
        -- Since the list is strictly increasing, for any i < j, we have xs[i]! < xs[j]!.
        intros i j hij hj_lt_length
        have h_strict_mono : ∀ i j : ℕ, i < j → j < xs.length → xs[i]! < xs[j]! := by
          intro i j hij hj_lt_length
          have h_sorted : List.Pairwise (· < ·) xs := h_precond
          have := List.pairwise_iff_get.mp h_sorted;
          convert this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij using 1;
          · grind;
          · grind;
        exact h_strict_mono i j hij hj_lt_length;
      grind;
    exact ⟨ h.1, h_all_before, h_all_after, h_count ⟩;
  · -- By definition of postcondition, we know that result is in the valid range and satisfies the ensures clauses.
    obtain ⟨h1, h2, h3, h4⟩ := h;
    refine' ⟨ h1, _, _ ⟩;
    · -- By definition of `ensures2`, for any `i < result`, `xs[i]! < target`.
      have h_all_lt : ∀ i < result, xs[i]! < target := by
        intros i hi
        have h_lt : i < xs.length := by
          -- Since `result ≤ xs.length` by `h1`, and `i < result` by `hi`, we can conclude `i < xs.length` by transitivity.
          apply lt_of_lt_of_le hi h1
        exact h2 i hi h_lt;
      aesop;
    · exact fun h => h3 _ le_rfl h