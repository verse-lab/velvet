/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 64c6feed-681c-444b-818b-c99e217309d5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.LongestCommonSubsequence_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Int) (h_precond : VerinaSpec.LongestCommonSubsequence_precond a b):
  VerinaSpec.LongestCommonSubsequence_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def intMax (x y : Int) : Int :=
  if x < y then y else x

@[reducible]
def LongestCommonSubsequence_postcond (a : Array Int) (b : Array Int) (result: Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq a
  let subseqB := allSubseq b
  let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length)
  commonSubseqLens.contains result ∧ commonSubseqLens.all (· ≤ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- A list s is a subsequence of list l if s can be obtained by deleting elements from l
-- We use List.Sublist from Mathlib which represents this concept
-- List.Sublist l₁ l₂ means l₁ is a sublist of l₂ (can delete elements from l₂ to get l₁)

-- Helper: check if a list is a common subsequence of two lists
def isCommonSubseq (s : List Int) (a : List Int) (b : List Int) : Prop :=
  s.Sublist a ∧ s.Sublist b

-- Helper: check if n is a valid LCS length for two lists
-- This means there exists a common subsequence of length n, and no common subsequence is longer
def isLCSLength (a : List Int) (b : List Int) (n : Nat) : Prop :=
  (∃ s : List Int, isCommonSubseq s a b ∧ s.length = n) ∧
  (∀ s : List Int, isCommonSubseq s a b → s.length ≤ n)

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- No preconditions required

def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  isLCSLength a.toList b.toList result.toNat

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.LongestCommonSubsequence_precond a b ↔ LeetProofSpec.precondition a b := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.LongestCommonSubsequence_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Int) (h_precond : VerinaSpec.LongestCommonSubsequence_precond a b):
  VerinaSpec.LongestCommonSubsequence_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · refine' ⟨ _, _ ⟩;
    · cases h ; aesop;
    · unfold VerinaSpec.LongestCommonSubsequence_postcond at h;
      -- Since `result` is in the list of common subsequence lengths, there exists a common subsequence of length `result`.
      obtain ⟨s, hs⟩ : ∃ s : List ℤ, s.Sublist a.toList ∧ s.Sublist b.toList ∧ s.length = result.toNat := by
        have h_subseq_b : ∀ (l : List ℤ), ∀ (s : List ℤ), s ∈ List.map List.reverse (List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] l) → s.Sublist l := by
          intros l s hs; induction' l using List.reverseRecOn with l ih generalizing s <;> aesop;
        aesop;
      refine' ⟨ ⟨ s, ⟨ hs.1, hs.2.1 ⟩, hs.2.2 ⟩, _ ⟩;
      intro s hs; have := h.2; simp_all +decide [ List.all_eq ] ;
      contrapose! this;
      -- Since $s$ is a common subsequence of $a$ and $b$, reversing $s$ gives a subsequence of both $a.reverse$ and $b.reverse$.
      have h_rev_subseq : s.reverse ∈ Array.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] a ∧ s.reverse ∈ Array.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] b := by
        have h_rev_subseq : ∀ (l : List ℤ) (s : List ℤ), s.Sublist l → s.reverse ∈ List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] l := by
          -- We can prove this by induction on the list $l$.
          intro l s hs
          induction' l with x l ih generalizing s;
          · aesop;
          · rcases hs with ( _ | ⟨ _, hs ⟩ ) <;> simp_all +decide [ List.sublist_cons_iff ];
            · have h_rev_subseq : ∀ (l : List ℤ) (s : List ℤ), s ∈ List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] l → s ∈ List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[], [x]] l := by
                intros l s hs; induction' l using List.reverseRecOn with x l ih generalizing s <;> aesop;
              exact h_rev_subseq _ _ ( ih _ hs );
            · have h_rev_subseq : ∀ (l : List ℤ) (s : List ℤ), s ∈ List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] l → s ++ [x] ∈ List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[], [x]] l := by
                intros l s hs; induction' l using List.reverseRecOn with x l ih generalizing s <;> aesop;
              exact h_rev_subseq _ _ ( ih _ ‹_› );
        exact ⟨ by simpa using h_rev_subseq _ _ hs.1, by simpa using h_rev_subseq _ _ hs.2 ⟩;
      exact ⟨ _, _, h_rev_subseq.1, h_rev_subseq.2, rfl, by linarith [ Int.toNat_of_nonneg ( show 0 ≤ result by linarith [ h.1.choose_spec.2 ] ) ] ⟩;
  · -- By definition of `h`, we know that `result` is the length of the longest common subsequence of `a.toList` and `b.toList`.
    obtain ⟨s, hs_subseq, hs_len⟩ : ∃ s : List ℤ, s.Sublist a.toList ∧ s.Sublist b.toList ∧ s.length = result.toNat := by
      obtain ⟨ s, hs_subseq, hs_len ⟩ := h.2.1;
      exact ⟨ s, hs_subseq.1, hs_subseq.2, hs_len ⟩;
    have h_subseq_list : ∀ l : List ℤ, l ∈ (a.toList.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) ↔ l.Sublist a.toList := by
      -- We can prove this by induction on the list `y`.
      have h_ind : ∀ y : List ℤ, ∀ l : List ℤ, l ∈ (y.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) ↔ l.Sublist y := by
        -- We'll use induction on the list `y`.
        intro y l
        induction' y using List.reverseRecOn with y ih generalizing l;
        · aesop;
        · simp_all +decide [ List.foldl_append ];
          constructor;
          · rintro ( h | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ List.sublist_append_right ];
            grind;
          · intro hl; rw [ List.sublist_append_iff ] at hl; aesop;
      exact h_ind _;
    have h_subseq_list_b : ∀ l : List ℤ, l ∈ (b.toList.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) ↔ l.Sublist b.toList := by
      -- By definition of `List.foldl`, the list generated by folding the function over `b.toList` is exactly the list of all sublists of `b.toList`.
      have h_foldl_sublists : ∀ (l : List ℤ), List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] l = List.map List.reverse (List.sublists l) := by
        intro l; induction' l using List.reverseRecOn with l ih <;> aesop;
      aesop;
    have h_subseq_list_common : ∀ l : List ℤ, l ∈ (a.toList.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse).filter (fun l => (b.toList.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse).contains l) ↔ l.Sublist a.toList ∧ l.Sublist b.toList := by
      simp_all +decide [ List.mem_filter ];
    constructor;
    · cases h ; aesop;
    · have h_subseq_list_common : ∀ l : List ℤ, l ∈ (a.toList.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse).filter (fun l => (b.toList.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse).contains l) → l.length ≤ result.toNat := by
        intros l hl
        have h_l_subseq : l.Sublist a.toList ∧ l.Sublist b.toList := by
          exact h_subseq_list_common l |>.1 hl;
        exact h.2.2 l ⟨ h_l_subseq.1, h_l_subseq.2 ⟩ |> le_trans <| by linarith;
      simp_all +decide [ List.all_eq ];
      -- By definition of `h_subseq_list_common`, we know that for any list `l` that is a sublist of both `a.toList` and `b.toList`, `l.length ≤ result.toNat`.
      intros x l hl_a hl_b hx
      have h_len : l.length ≤ result.toNat := h_subseq_list_common l hl_a hl_b
      have h_le : x ≤ result := by
        linarith [ Int.toNat_of_nonneg ( show 0 ≤ result by linarith [ h.1 ] ) ]
      exact h_le