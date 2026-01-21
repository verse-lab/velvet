/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8a6dfbd8-9802-4244-827a-db697afdaa9c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.lengthOfLIS_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Nat) (h_precond : VerinaSpec.lengthOfLIS_precond nums):
  VerinaSpec.lengthOfLIS_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic
import Mathlib.Data.List.Basic


namespace VerinaSpec

@[reducible]
def lengthOfLIS_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def maxInArray (arr : Array Nat) : Nat :=
  arr.foldl (fun a b => if a ≥ b then a else b) 0

@[reducible]
def lengthOfLIS_postcond (nums : List Int) (result: Nat) (h_precond : lengthOfLIS_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a list is strictly increasing using Mathlib's Pairwise
def isStrictlyIncreasing (l : List Int) : Prop :=
  l.Pairwise (· < ·)

-- Helper: Check if one list is a subsequence of another using Mathlib's Sublist
-- A subsequence preserves relative order (can delete elements but not reorder)
def isStrictlyIncreasingSubseq (sub : List Int) (original : List Int) : Prop :=
  sub.Sublist original ∧ isStrictlyIncreasing sub

-- Postcondition clauses
-- 1. The result is achievable: there exists a strictly increasing subsequence of that length
def ensures1 (nums : List Int) (result : Nat) : Prop :=
  ∃ sub : List Int, isStrictlyIncreasingSubseq sub nums ∧ sub.length = result

-- 2. The result is maximal: no strictly increasing subsequence has greater length
def ensures2 (nums : List Int) (result : Nat) : Prop :=
  ∀ sub : List Int, isStrictlyIncreasingSubseq sub nums → sub.length ≤ result

def precondition (nums : List Int) : Prop :=
  True

-- no preconditions needed

def postcondition (nums : List Int) (result : Nat) : Prop :=
  ensures1 nums result ∧ ensures2 nums result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.lengthOfLIS_precond nums ↔ LeetProofSpec.precondition nums := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.lengthOfLIS_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (nums : List Int) (result : Nat) (h_precond : VerinaSpec.lengthOfLIS_precond nums):
  VerinaSpec.lengthOfLIS_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  constructor <;> intro h;
  · -- By definition of `lengthOfLIS_postcond`, there exists a subsequence of `nums` with length `result` that is strictly increasing.
    obtain ⟨sub, h_sub⟩ : ∃ sub : List Int, sub.Sublist nums ∧ sub.Pairwise (· < ·) ∧ sub.length = result := by
      -- By definition of `lengthOfLIS_postcond`, there exists a subsequence in the list of all subsequences with length `result`.
      obtain ⟨sub, h_sub⟩ : ∃ sub : List Int, sub ∈ (nums.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) ∧ List.Pairwise (· < ·) sub ∧ sub.length = result := by
        unfold VerinaSpec.lengthOfLIS_postcond at h; aesop;
      -- By definition of `foldl`, every element in the list of subsequences is a subsequence of `nums`.
      have h_subseq : ∀ {xs : List ℤ}, ∀ sub ∈ List.map List.reverse (List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] xs), sub.Sublist xs := by
        intros xs sub h_sub; induction' xs using List.reverseRecOn with xs ih generalizing sub <;> aesop;
      exact ⟨ sub, h_subseq sub h_sub.1, h_sub.2.1, h_sub.2.2 ⟩;
    have h_max : ∀ sub' : List Int, sub'.Sublist nums → sub'.Pairwise (· < ·) → sub'.length ≤ result := by
      intro sub' h_sub' h_sub'_inc
      have h_sub'_in_allSubseq : sub' ∈ (nums.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) := by
        have h_sub'_in_allSubseq : ∀ {l : List ℤ} {sub : List ℤ}, sub.Sublist l → sub ∈ List.map List.reverse (List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] l) := by
          intros l sub h_sub; induction' l using List.reverseRecOn with l ih generalizing sub; aesop;
          rw [ List.sublist_append_iff ] at h_sub ; aesop;
        exact h_sub'_in_allSubseq h_sub';
      have h_sub'_in_increasingSubseqLens : sub'.length ∈ (List.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] nums |>.map List.reverse |>.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)) := by
        rw [ List.mem_map ] at *; aesop;
      grind;
    exact ⟨ ⟨ sub, ⟨ h_sub.1, h_sub.2.1 ⟩, h_sub.2.2 ⟩, fun sub' h_sub' => h_max sub' h_sub'.1 h_sub'.2 ⟩;
  · -- To prove the first part, we need to show that there exists a subsequence of length result in the list of all subsequences.
    have h_exists : ∃ subseq ∈ List.map List.reverse ((List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] nums)), List.Pairwise (fun x1 x2 => x1 < x2) subseq ∧ subseq.length = result := by
      -- By definition of `h`, there exists a subsequence `sub` of `nums` that is strictly increasing and has length `result`.
      obtain ⟨sub, hsub⟩ := h.left;
      -- Since `sub` is a subsequence of `nums`, it must be included in the list of all subsequences generated by the foldl operation.
      have h_subseq : sub.reverse ∈ List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] nums := by
        have h_subseq : ∀ {l : List ℤ} {sub : List ℤ}, sub.Sublist l → sub.reverse ∈ List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] l := by
          intros l sub hsub; induction' l using List.reverseRecOn with l ih generalizing sub; aesop;
          rw [ List.sublist_append_iff ] at hsub ; aesop;
        exact h_subseq hsub.1.1;
      unfold LeetProofSpec.isStrictlyIncreasingSubseq at hsub; aesop;
    -- To prove the second part, we need to show that all elements in the list of lengths of increasing subsequences are less than or equal to result.
    have h_all_le : ∀ subseq ∈ List.map List.reverse ((List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] nums)), List.Pairwise (fun x1 x2 => x1 < x2) subseq → subseq.length ≤ result := by
      intro subseq hsubseq hpairwise
      have h_subseq : subseq.Sublist nums := by
        have h_subseq : ∀ (l : List ℤ), ∀ (subseq : List ℤ), subseq ∈ List.map List.reverse ((List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] l)) → subseq.Sublist l := by
          intros l subseq hsubseq; induction' l using List.reverseRecOn with l ih generalizing subseq <;> aesop;
        exact h_subseq _ _ hsubseq;
      exact h.2 subseq ⟨ h_subseq, hpairwise ⟩;
    grind