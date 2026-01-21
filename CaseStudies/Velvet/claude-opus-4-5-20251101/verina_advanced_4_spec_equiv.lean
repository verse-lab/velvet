/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b4204d95-f2ae-44ff-a2c5-dbaa719fa133

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.LongestIncreasingSubsequence_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.LongestIncreasingSubsequence_precond a):
  VerinaSpec.LongestIncreasingSubsequence_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def LongestIncreasingSubsequence_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def intMax (x y : Int) : Int :=
  if x < y then y else x

def LongestIncreasingSubsequence_postcond (a : Array Int) (result: Int) (h_precond : LongestIncreasingSubsequence_precond (a)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (a.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Check if a list is strictly increasing using Mathlib's List.Chain'
-- This avoids explicit recursion
def isStrictlyIncreasing (sub : List Int) : Prop :=
  List.Chain' (· < ·) sub

-- Check if one list is a subsequence of another (preserves order, allows gaps)
-- Using Mathlib's List.Sublist
def isIncreasingSubseqOf (sub : List Int) (arr : Array Int) : Prop :=
  sub.Sublist arr.toList ∧ isStrictlyIncreasing sub

-- Precondition: no restrictions on input array
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is the length of the longest increasing subsequence
-- 1. Result is non-negative
-- 2. There exists an increasing subsequence of that length
-- 3. No increasing subsequence has length greater than result
def postcondition (a : Array Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ sub : List Int, isIncreasingSubseqOf sub a ∧ sub.length = result.toNat) ∧
  (∀ sub : List Int, isIncreasingSubseqOf sub a → sub.length ≤ result.toNat)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.LongestIncreasingSubsequence_precond a ↔ LeetProofSpec.precondition a := by
  -- Since both preconditions are always true, the equivalence holds trivially.
  simp [VerinaSpec.LongestIncreasingSubsequence_precond, LeetProofSpec.precondition]

noncomputable section AristotleLemmas

/-
The `foldl` operation in `VerinaSpec` generates all subsequences of the reversed list. Specifically, if we fold over `l`, the resulting list contains `sub` if and only if `sub` is a sublist of `l.reverse`.
-/
theorem foldl_subseqs_aux (l : List Int) (sub : List Int) :
  sub ∈ l.foldl (fun acc x => acc ++ acc.map (fun s => x :: s)) [[]] ↔ sub.Sublist l.reverse := by
  induction' l using List.reverseRecOn with l ih generalizing sub <;> simp +decide [ *, List.foldl ];
  constructor;
  · aesop;
  · intro h;
    cases h <;> aesop

/-
The `allSubseq` construction in `VerinaSpec` generates exactly the subsequences of `a`.
This follows from `foldl_subseqs_aux` and the property that `sub.reverse.Sublist l.reverse ↔ sub.Sublist l`.
-/
theorem allSubseq_correct (a : Array Int) (sub : List Int) :
  sub ∈ (a.foldl (fun acc x => acc ++ acc.map (fun s => x :: s)) [[]] |>.map List.reverse) ↔ sub.Sublist a.toList := by
  convert foldl_subseqs_aux a.toList sub.reverse using 1 ; aesop;
  exact?

/-
`List.Pairwise (<)` is equivalent to `isStrictlyIncreasing` (which uses `Chain'`). This is a direct application of `List.chain'_iff_pairwise`.
-/
theorem pairwise_increasing_iff (sub : List Int) :
  List.Pairwise (· < ·) sub ↔ LeetProofSpec.isStrictlyIncreasing sub := by
  -- The pairwise condition and the chain' condition are equivalent because they both ensure that each element is less than the next.
  simp [LeetProofSpec.isStrictlyIncreasing, List.Chain'];
  exact?

end AristotleLemmas

theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.LongestIncreasingSubsequence_precond a):
  VerinaSpec.LongestIncreasingSubsequence_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  unfold VerinaSpec.LongestIncreasingSubsequence_postcond LeetProofSpec.postcondition;
  constructor <;> intro h;
  · -- By definition of `allSubseq`, we know that `result` is the length of some increasing subsequence of `a`.
    obtain ⟨sub, h_sub⟩ : ∃ sub : List ℤ, sub ∈ (a.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) ∧ sub.length = result.toNat ∧ List.Pairwise (· < ·) sub := by
      have := List.mem_map.mp ( show result ∈ List.map ( fun x : List ℤ => ( x.length : ℤ ) ) ( List.filter ( fun l : List ℤ => Decidable.decide ( List.Pairwise ( fun x1 x2 : ℤ => x1 < x2 ) l ) ) ( List.map List.reverse ( Array.foldl ( fun ( acc : List ( List ℤ ) ) ( x : ℤ ) => acc ++ List.map ( fun ( sub : List ℤ ) => x :: sub ) acc ) [ [ ] ] a ) ) ) from by aesop ) ; aesop;
    refine' ⟨ _, _, _ ⟩;
    · grind;
    · -- By definition of `allSubseq`, we know that `sub` is a subsequence of `a`.
      have h_subseq : sub.Sublist a.toList := by
        exact allSubseq_correct a sub |>.1 h_sub.1;
      exact ⟨ sub, ⟨ h_subseq, by simpa [ pairwise_increasing_iff ] using h_sub.2.2 ⟩, h_sub.2.1 ⟩;
    · intro sub' h_sub'
      have h_sub'_in_allSubseq : sub' ∈ (a.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) := by
        apply (allSubseq_correct a sub').mpr;
        exact h_sub'.1;
      have h_sub'_in_increasingSubseqLens : sub' ∈ (a.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) ∧ List.Pairwise (· < ·) sub' := by
        exact ⟨ h_sub'_in_allSubseq, by simpa using pairwise_increasing_iff sub' |>.2 h_sub'.2 ⟩;
      have h_sub'_in_increasingSubseqLens : (sub'.length : ℤ) ∈ List.map (fun x => x.length : List ℤ → ℤ) (List.filter (fun l => List.Pairwise (· < ·) l) (a.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse)) := by
        exact List.mem_map.mpr ⟨ sub', List.mem_filter.mpr ⟨ h_sub'_in_increasingSubseqLens.1, by simpa using h_sub'_in_increasingSubseqLens.2 ⟩, rfl ⟩;
      grind;
  · constructor;
    · obtain ⟨ sub, hsub₁, hsub₂ ⟩ := h.2.1;
      have h_subseq : sub.Sublist a.toList := by
        exact hsub₁.1;
      have h_subseq : sub ∈ (a.foldl (fun acc x => acc ++ acc.map (fun s => x :: s)) [[]] |>.map List.reverse) := by
        exact?;
      have h_subseq : List.Pairwise (· < ·) sub := by
        exact pairwise_increasing_iff sub |>.2 hsub₁.2;
      aesop;
    · -- By definition of `isIncreasingSubseqOf`, we know that `sub` is a sublist of `a` and is strictly increasing.
      have h_subseq : ∀ sub : List ℤ, sub.Sublist a.toList → List.Pairwise (· < ·) sub → sub.length ≤ result.toNat := by
        exact fun sub hsub hsub' => h.2.2 sub ⟨ hsub, by simpa [ pairwise_increasing_iff ] using hsub' ⟩;
      -- Apply `h_subseq` to each element in the list to show that they are all less than or equal to `result`.
      have h_all_le : ∀ sub ∈ (a.foldl (fun acc x => acc ++ acc.map (fun s => x :: s)) [[]] |>.map List.reverse), List.Pairwise (· < ·) sub → sub.length ≤ result.toNat := by
        have h_all_le : ∀ sub ∈ (a.foldl (fun acc x => acc ++ acc.map (fun s => x :: s)) [[]] |>.map List.reverse), sub.Sublist a.toList := by
          exact?;
        exact fun sub hsub hsub' => h_subseq sub ( h_all_le sub hsub ) hsub';
      grind