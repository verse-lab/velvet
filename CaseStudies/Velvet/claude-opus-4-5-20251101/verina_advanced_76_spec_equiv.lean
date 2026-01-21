/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c46940e5-85d5-4636-8b83-bfc745d8ef6f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) (k : Nat):
  VerinaSpec.topKFrequent_precond nums k ↔ LeetProofSpec.precondition nums k

- theorem postcondition_equiv (nums : List Int) (k : Nat) (result : List Int) (h_precond : VerinaSpec.topKFrequent_precond nums k):
  VerinaSpec.topKFrequent_postcond nums k result h_precond ↔ LeetProofSpec.postcondition nums k result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def topKFrequent_precond (nums : List Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k ≤ nums.eraseDups.length

-- !benchmark @end precond

@[reducible]
def topKFrequent_postcond (nums : List Int) (k : Nat) (result: List Int) (h_precond : topKFrequent_precond (nums) (k)) : Prop :=
  -- !benchmark @start postcond
  -- Result contains exactly k elements
  result.length = k ∧

  -- All elements in result appear in the original list
  result.all (· ∈ nums) ∧

  -- All elements in result are distinct
  List.Pairwise (· ≠ ·) result ∧

  -- For any element in result and any element not in result, the frequency of the
  -- element in result is greater or equal (simplified: no tie-breaking constraint on ordering)
  (result.all (fun x =>
    nums.all (fun y =>
      y ∈ result ∨ nums.count x ≥ nums.count y
    ))) ∧

  -- Elements in result are ordered by non-increasing frequency
  List.Pairwise (fun (x, i) (y, j) =>
    i < j → nums.count x ≥ nums.count y
  ) result.zipIdx

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Count occurrences of an element in a list (using List.count from Mathlib)
def countFreq (x : Int) (nums : List Int) : Nat :=
  nums.count x

-- Get the list of distinct elements
def distinctElements (nums : List Int) : List Int :=
  nums.eraseDups

-- Check if result is sorted by frequency in descending order
def isSortedByFreqDesc (result : List Int) (nums : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < result.length →
    countFreq result[i]! nums ≥ countFreq result[j]! nums

-- Precondition: k is at most the number of distinct elements
def precondition (nums : List Int) (k : Nat) : Prop :=
  k ≤ (distinctElements nums).length

-- Postcondition clauses
-- 1. Result has exactly k elements
def ensures1 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  result.length = k

-- 2. All elements in result are from the original list
def ensures2 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ∀ x ∈ result, x ∈ nums

-- 3. Result contains no duplicates
def ensures3 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  result.Nodup

-- 4. Result is sorted by frequency (descending)
def ensures4 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  isSortedByFreqDesc result nums

-- 5. Any element not in result has frequency at most the minimum frequency in result
def ensures5 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ∀ x ∈ nums, x ∉ result →
    ∀ y ∈ result, countFreq x nums ≤ countFreq y nums

def postcondition (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ensures1 nums k result ∧
  ensures2 nums k result ∧
  ensures3 nums k result ∧
  ensures4 nums k result ∧
  ensures5 nums k result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int) (k : Nat):
  VerinaSpec.topKFrequent_precond nums k ↔ LeetProofSpec.precondition nums k := by
  rfl

theorem postcondition_equiv (nums : List Int) (k : Nat) (result : List Int) (h_precond : VerinaSpec.topKFrequent_precond nums k):
  VerinaSpec.topKFrequent_postcond nums k result h_precond ↔ LeetProofSpec.postcondition nums k result := by
  -- To prove the equivalence, we can show that each part of Verina's postcondition is equivalent to a part of LeetProof's postcondition.
  apply Iff.intro;
  · -- By definition of `topKFrequent_postcond`, if it holds, then `result` has length `k`, all elements of `result` are in `nums`, `result` is pairwise distinct, and for any element `x` in `result` and any element `y` not in `result`, the frequency of `x` is at least the frequency of `y`.
    intro h
    obtain ⟨h_len, h_all, h_pairwise, h_freq⟩ := h;
    -- By definition of `isSortedByFreqDesc`, the pairwise condition in `h_freq` implies that the result is sorted by frequency in descending order.
    have h_sorted : LeetProofSpec.isSortedByFreqDesc result nums := by
      -- By definition of `isSortedByFreqDesc`, the pairwise condition in `h_freq` implies that the result is sorted by frequency in descending order. We can use the fact that if i < j, then the count of the element at i is at least the count of the element at j.
      intros i j hij hj;
      have := List.pairwise_iff_get.mp h_freq.2;
      convert this ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ ( Nat.lt_of_le_of_lt ( Nat.le_refl _ ) hij ) _;
      · grind;
      · grind;
      · grind;
    -- By combining the results from h_len, h_all, h_pairwise, and h_sorted, we can conclude the proof.
    apply And.intro h_len;
    refine' ⟨ _, _, h_sorted, _ ⟩;
    · intro x hx; aesop;
    · exact?;
    · intro x hx hx'; simp_all +decide [ List.all_eq_true ] ;
      intro y hy; specialize h_freq; have := h_freq.1 y hy x hx; aesop;
  · intro h_postcond;
    -- By definition of `postcondition`, we know that `result` is a length `k` list of `nums` elements (without duplicates), and that it's sorted decreasingly by frequency.
    obtain ⟨h_length, h_elements, h_nodup, h_sorted, h_min_freq⟩ := h_postcond;
    -- By combining the results from h_length, h_elements, h_nodup, h_sorted, and h_min_freq, we can conclude that the postcondition holds.
    apply And.intro h_length
    apply And.intro (by
    aesop) (by
    -- Since the result list is nodup, any two elements in the list must be different.
    have h_pairwise_ne : List.Pairwise (fun x y => x ≠ y) result := by
      exact h_nodup;
    refine' ⟨ h_pairwise_ne, _, _ ⟩;
    · simp_all +decide [ List.all_eq_true ];
      exact fun x hx y hy => Classical.or_iff_not_imp_left.2 fun hy' => h_min_freq y hy hy' x hx;
    · -- Since the result list is sorted in descending order of frequency, for any i < j, the count of the element at i is greater than or equal to the count at j.
      have h_sorted_counts : ∀ i j : ℕ, i < j → j < result.length → List.count (result[i]!) nums ≥ List.count (result[j]!) nums := by
        exact?;
      -- By definition of `List.zipIdx`, the elements of the zipped list are pairs `(x, i)` where `x` is an element of `result` and `i` is its index.
      have h_zipIdx : List.zipIdx result = List.map (fun (p : ℤ × ℕ) => (p.1, p.2)) (List.zip result (List.range result.length)) := by
        refine' List.ext_get _ _ <;> aesop;
      rw [ List.pairwise_iff_get ];
      grind)