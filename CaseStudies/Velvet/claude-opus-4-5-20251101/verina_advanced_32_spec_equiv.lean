/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: db6a9ed4-7f17-42ca-b4b0-196c22e1a718

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (numbers : List Int):
  VerinaSpec.longestIncreasingSubsequence_precond numbers ↔ LeetProofSpec.precondition numbers

- theorem postcondition_equiv (numbers : List Int) (result : Nat) (h_precond : VerinaSpec.longestIncreasingSubsequence_precond numbers):
  VerinaSpec.longestIncreasingSubsequence_postcond numbers result h_precond ↔ LeetProofSpec.postcondition numbers result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def longestIncreasingSubsequence_precond (numbers : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def longestIncreasingSubsequence_postcond (numbers : List Int) (result: Nat) (h_precond : longestIncreasingSubsequence_precond (numbers)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (numbers.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a list of integers is strictly increasing
def isStrictlyIncreasing : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x < y ∧ isStrictlyIncreasing (y :: rest)

-- Helper: Check if one list is a subsequence of another (preserves order, may skip elements)
def isSubsequenceOf : List Int → List Int → Prop
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys => 
    if x = y then isSubsequenceOf xs ys
    else isSubsequenceOf (x :: xs) ys

-- Helper: Check if a list is a valid increasing subsequence of another list
def isIncreasingSubsequenceOf (subseq : List Int) (original : List Int) : Prop :=
  isSubsequenceOf subseq original ∧ isStrictlyIncreasing subseq

-- Precondition: No constraints on input
def precondition (numbers : List Int) : Prop :=
  True

-- Postcondition: result is the length of the longest increasing subsequence
-- Properties:
-- 1. There exists an increasing subsequence of this length
-- 2. No increasing subsequence has greater length
-- 3. Result bounds: 0 for empty list, at least 1 for non-empty, at most list length
def postcondition (numbers : List Int) (result : Nat) : Prop :=
  -- There exists an increasing subsequence of length result
  (∃ subseq : List Int, 
    isIncreasingSubsequenceOf subseq numbers ∧ 
    subseq.length = result) ∧
  -- No increasing subsequence has greater length
  (∀ subseq : List Int, 
    isIncreasingSubsequenceOf subseq numbers → 
    subseq.length ≤ result) ∧
  -- Result is 0 iff list is empty
  (numbers = [] ↔ result = 0)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (numbers : List Int):
  VerinaSpec.longestIncreasingSubsequence_precond numbers ↔ LeetProofSpec.precondition numbers := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.longestIncreasingSubsequence_precond, LeetProofSpec.precondition]

noncomputable section AristotleLemmas

/-
LeetProofSpec.isStrictlyIncreasing is equivalent to List.Pairwise (· < ·).
-/
theorem isStrictlyIncreasing_iff_pairwise (l : List Int) : LeetProofSpec.isStrictlyIncreasing l ↔ List.Pairwise (· < ·) l := by
  -- We'll use induction on the list to prove the equivalence.
  induction' l with x l ih;
  · exact iff_of_true trivial ( List.Pairwise.nil );
  · -- We'll use induction on `l` to prove the equivalence.
    induction' l with y l ih generalizing x;
    · aesop;
    · simp_all +decide [ List.pairwise_cons ];
      -- By definition of StrictlyIncreasing, we have that x < y and the rest of the list is strictly increasing.
      have h_def : LeetProofSpec.isStrictlyIncreasing (x :: y :: l) ↔ x < y ∧ LeetProofSpec.isStrictlyIncreasing (y :: l) := by
        exact?;
      grind

/-
`LeetProofSpec.isSubsequenceOf` is equivalent to `List.Sublist`.
-/
theorem isSubsequenceOf_iff_sublist (l1 l2 : List Int) :
  LeetProofSpec.isSubsequenceOf l1 l2 ↔ List.Sublist l1 l2 := by
    -- We'll use induction on the list l2.
    induction' l2 with y ys ih generalizing l1;
    · cases l1 <;> tauto;
    · rcases l1 with ( _ | ⟨ x, xs ⟩ ) <;> simp_all +decide [ List.sublist_cons_iff ];
      · exact?;
      · have h_def : LeetProofSpec.isSubsequenceOf (x :: xs) (y :: ys) = (if x = y then LeetProofSpec.isSubsequenceOf xs ys else LeetProofSpec.isSubsequenceOf (x :: xs) ys) := by
          exact?;
        split_ifs at h_def <;> simp_all +decide;
        exact fun h => List.Sublist.trans ( List.sublist_cons_self _ _ ) h

/-
The `foldl` operation in `VerinaSpec` produces exactly the reversed subsequences of the input list.
-/
theorem verina_subsequences_correct (numbers : List Int) (sub : List Int) :
  sub ∈ (numbers.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]]) ↔ List.Sublist sub.reverse numbers := by
    induction' numbers using List.reverseRecOn with x xs ih generalizing sub ; aesop;
    constructor;
    · aesop;
    · rw [ List.sublist_append_iff ];
      aesop

end AristotleLemmas

theorem postcondition_equiv (numbers : List Int) (result : Nat) (h_precond : VerinaSpec.longestIncreasingSubsequence_precond numbers):
  VerinaSpec.longestIncreasingSubsequence_postcond numbers result h_precond ↔ LeetProofSpec.postcondition numbers result := by
  constructor <;> intro h;
  · constructor;
    · obtain ⟨subseq, h_subseq⟩ : ∃ subseq ∈ (numbers.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse), List.Pairwise (· < ·) subseq ∧ subseq.length = result := by
        unfold VerinaSpec.longestIncreasingSubsequence_postcond at h; aesop;
      -- By definition of `isSubsequenceOf`, we know that `subseq` is a subsequence of `numbers`.
      have h_subseq_sublist : List.Sublist subseq numbers := by
        have := verina_subsequences_correct numbers subseq.reverse; aesop;
      exact ⟨ subseq, ⟨ isSubsequenceOf_iff_sublist _ _ |>.2 h_subseq_sublist, isStrictlyIncreasing_iff_pairwise _ |>.2 h_subseq.2.1 ⟩, h_subseq.2.2 ⟩;
    · unfold VerinaSpec.longestIncreasingSubsequence_postcond at h;
      constructor;
      · intro subseq h_subseq
        obtain ⟨h_subseq_sublist, h_subseq_pairwise⟩ := h_subseq;
        have h_subseq_increasing : subseq.reverse ∈ (numbers.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]]) := by
          rw [ isSubsequenceOf_iff_sublist ] at h_subseq_sublist;
          have := verina_subsequences_correct numbers subseq.reverse; aesop;
        have h_subseq_increasing : subseq.reverse.length ∈ List.map (fun x => x.length) (List.filter (fun l => List.Pairwise (· < ·) l) (List.map List.reverse ((fun (init : List (List ℤ)) => List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) init numbers) [[]]))) := by
          simp_all +decide [ List.mem_map, List.mem_filter ];
          exact ⟨ subseq, ⟨ h_subseq_increasing, by simpa [ List.pairwise_reverse ] using isStrictlyIncreasing_iff_pairwise subseq |>.1 h_subseq_pairwise ⟩, rfl ⟩;
        grind;
      · induction numbers using List.reverseRecOn <;> aesop;
  · -- Let's obtain the subsequence `subseq` from the hypothesis `h`.
    obtain ⟨subseq, h_subseq_inc, h_subseq_len⟩ := h.left;
    constructor;
    · -- By definition of `isStrictlyIncreasing`, we know that `subseq` is a subsequence of `numbers` and is strictly increasing.
      have h_subseq_sublist : List.Sublist subseq numbers ∧ List.Pairwise (· < ·) subseq := by
        exact ⟨ by exact ( isSubsequenceOf_iff_sublist subseq numbers ) |>.1 h_subseq_inc.1, by exact ( isStrictlyIncreasing_iff_pairwise subseq ) |>.1 h_subseq_inc.2 ⟩;
      have := verina_subsequences_correct numbers subseq.reverse; aesop;
    · -- By definition of `isSubsequenceOf`, any subsequence of `numbers` that is strictly increasing must be a sublist of `numbers`.
      have h_subseq_sublist : ∀ (sub : List ℤ), List.Sublist sub numbers → List.Pairwise (· < ·) sub → sub.length ≤ result := by
        intros sub h_sub_sublist h_sub_inc
        apply h.right.left sub;
        constructor;
        · convert h_sub_sublist using 1;
          ext; exact?;
        · have h_subseq_inc : ∀ (l : List ℤ), List.Pairwise (· < ·) l → LeetProofSpec.isStrictlyIncreasing l := by
            intros l hl; exact (by
            convert hl using 1;
            ext l; exact isStrictlyIncreasing_iff_pairwise l;);
          exact h_subseq_inc sub h_sub_inc;
      simp_all +decide [ List.all_eq ];
      intros x sub h_sub h_sub_inc h_sub_len;
      have := verina_subsequences_correct numbers sub.reverse; aesop;