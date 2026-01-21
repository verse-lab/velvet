/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 86177fb2-2002-417a-a485-f252374aec64

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.lengthOfLIS_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.lengthOfLIS_precond nums):
  VerinaSpec.lengthOfLIS_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def lengthOfLIS_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def lengthOfLIS_postcond (nums : List Int) (result: Int) (h_precond : lengthOfLIS_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  -- Helper function to check strictly increasing
  let rec isStrictlyIncreasing (l : List Int) : Bool :=
    match l with
    | [] | [_] => true
    | x :: y :: rest => x < y && isStrictlyIncreasing (y :: rest)

  -- Generate all subsequences
  let rec subsequences (xs : List Int) : List (List Int) :=
    match xs with
    | [] => [[]]
    | x :: xs' =>
      let rest := subsequences xs'
      rest ++ rest.map (fun r => x :: r)

  let allIncreasing := subsequences nums |>.filter (fun l => isStrictlyIncreasing l)

  allIncreasing.any (fun l => l.length = result) ∧
  allIncreasing.all (fun l => l.length ≤ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a list is strictly increasing
def isStrictlyIncreasing (l : List Int) : Prop :=
  ∀ i : Nat, i + 1 < l.length → l[i]! < l[i + 1]!

-- Helper: Check if one list is a subsequence of another (preserves order, not necessarily contiguous)
-- A subsequence can be obtained by deleting some elements from the original list
def isSubseqOf (sub : List Int) (main : List Int) : Prop :=
  sub.Sublist main

-- Helper: Check if a list is a valid strictly increasing subsequence of the given list
def isIncreasingSubseqOf (sub : List Int) (main : List Int) : Prop :=
  isSubseqOf sub main ∧ isStrictlyIncreasing sub

-- Precondition: no specific requirements on input
def precondition (nums : List Int) : Prop :=
  True

-- Postcondition: result is the length of the longest strictly increasing subsequence
-- 1. There exists a strictly increasing subsequence of nums with length equal to result
-- 2. No strictly increasing subsequence of nums has length greater than result
def postcondition (nums : List Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ sub : List Int, isIncreasingSubseqOf sub nums ∧ sub.length = result.toNat) ∧
  (∀ sub : List Int, isIncreasingSubseqOf sub nums → sub.length ≤ result.toNat)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.lengthOfLIS_precond nums ↔ LeetProofSpec.precondition nums := by
  -- Since both preconditions are trivially true, the equivalence holds.
  simp [VerinaSpec.lengthOfLIS_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.lengthOfLIS_precond nums):
  VerinaSpec.lengthOfLIS_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  constructor <;> intro h;
  · refine' ⟨ _, _, _ ⟩;
    · cases h ; aesop;
    · cases' h with h1 h2;
      -- Let's obtain such a subsequence from the hypothesis.
      obtain ⟨sub, hsub⟩ : ∃ sub : List ℤ, sub ∈ List.filter (fun l => VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing l) (VerinaSpec.lengthOfLIS_postcond.subsequences nums) ∧ sub.length = result.toNat := by
        aesop;
      -- Since sub is in the filtered list of subsequences, it is a subsequence of nums.
      have h_subseq : sub.Sublist nums := by
        have h_subseq : ∀ {l : List ℤ}, sub ∈ VerinaSpec.lengthOfLIS_postcond.subsequences l → sub.Sublist l := by
          -- By definition of subsequences, every element in the list of subsequences of l is a subsequence of l.
          intros l hl
          induction' l with x l ih;
          · cases hl;
            · trivial;
            · contradiction;
          · simp_all +decide [ VerinaSpec.lengthOfLIS_postcond.subsequences ];
            rcases hl with ( hl | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ List.sublist_cons_iff ];
            have h_subseq : ∀ {l : List ℤ}, ∀ a ∈ VerinaSpec.lengthOfLIS_postcond.subsequences l, a.Sublist l := by
              intros l a ha; induction' l with x l ih generalizing a <;> simp_all +decide [ VerinaSpec.lengthOfLIS_postcond.subsequences ] ;
              rcases ha with ( ha | ⟨ b, hb, rfl ⟩ ) <;> [ exact List.Sublist.trans ( ih _ ha ) ( List.sublist_cons_self _ _ ) ; exact List.Sublist.cons₂ _ ( ih _ hb ) ];
            exact Or.inr ( h_subseq a ha );
        exact h_subseq <| List.mem_of_mem_filter hsub.1;
      refine' ⟨ sub, ⟨ h_subseq, _ ⟩, hsub.2 ⟩;
      have h_strict_mono : ∀ l : List ℤ, VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing l ↔ ∀ i : Nat, i + 1 < l.length → l[i]! < l[i + 1]! := by
        intro l;
        induction' l with x l ih;
        · simp +decide;
        · rcases l with ( _ | ⟨ y, l ⟩ ) <;> simp_all +decide [ VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing ];
          constructor <;> intro h <;> simp_all +decide [ Nat.lt_succ_iff ];
          · grind;
          · exact ⟨ by simpa using h 0 ( Nat.zero_le _ ), fun i hi => by simpa using h ( i + 1 ) ( by linarith ) ⟩;
      exact h_strict_mono sub |>.1 ( List.mem_filter.mp hsub.1 |>.2 );
    · -- By definition of `VerinaSpec.lengthOfLIS_postcond`, if `sub` is an increasing subsequence of `nums`, then `sub` must be in the list of all increasing subsequences of `nums`.
      intro sub h_sub
      obtain ⟨h_subseq, h_incr⟩ := h_sub;
      have h_subseq_increasing : sub ∈ List.filter (fun l => VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing l) (VerinaSpec.lengthOfLIS_postcond.subsequences nums) := by
        have h_subseq_increasing : sub ∈ VerinaSpec.lengthOfLIS_postcond.subsequences nums := by
          have h_subseq_increasing : ∀ {xs ys : List ℤ}, xs.Sublist ys → xs ∈ VerinaSpec.lengthOfLIS_postcond.subsequences ys := by
            -- We can prove this by induction on the list `ys`.
            intro xs ys h_subseq
            induction' ys with y ys ih generalizing xs;
            · cases h_subseq ; tauto;
            · -- If `xs` is a sublist of `y :: ys`, then either `xs` is a sublist of `ys` or `xs` is `y` followed by a sublist of `ys`.
              by_cases hxs : xs.Sublist ys;
              · -- If `xs` is a sublist of `ys`, then by the induction hypothesis, `xs` is in the subsequences of `ys`.
                have hxs_in_ys : xs ∈ VerinaSpec.lengthOfLIS_postcond.subsequences ys := by
                  exact ih hxs;
                exact List.mem_append_left _ hxs_in_ys;
              · cases h_subseq ; aesop;
                exact List.mem_append_right _ ( List.mem_map.mpr ⟨ _, ih ‹_›, rfl ⟩ );
          exact h_subseq_increasing h_subseq;
        rw [ List.mem_filter ];
        -- By definition of `isStrictlyIncreasing`, we need to show that for every `i`, if `i + 1` is less than the length of `sub`, then `sub[i]! < sub[i + 1]!`.
        have h_strictly_increasing : ∀ i : Nat, i + 1 < sub.length → sub[i]! < sub[i + 1]! := by
          exact?;
        -- By definition of `isStrictlyIncreasing`, we need to show that for every `i`, if `i + 1` is less than the length of `sub`, then `sub[i]! < sub[i + 1]!`. This is exactly what `h_strictly_increasing` states.
        have h_strictly_increasing_def : ∀ {l : List ℤ}, (∀ i : Nat, i + 1 < l.length → l[i]! < l[i + 1]!) → VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing l := by
          -- We'll use induction on the list to prove that if the condition holds for all i, then the list is strictly increasing.
          intro l hl
          induction' l with x l ih;
          · rfl;
          · cases l <;> simp_all +decide [ VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing ];
            exact ⟨ by simpa using hl 0, ih fun i hi => by simpa using hl ( i + 1 ) ( by linarith ) ⟩;
        exact ⟨ h_subseq_increasing, h_strictly_increasing_def h_strictly_increasing ⟩;
      have := h.2;
      grind;
  · revert h;
    unfold LeetProofSpec.postcondition VerinaSpec.lengthOfLIS_postcond;
    -- If there exists a subsequence of length `result` and no longer subsequence, then the longest strictly increasing subsequence must have length `result`.
    intro h
    obtain ⟨sub, hsub_inc, hsub_len⟩ := h.right.left;
    have h_subseq : ∀ l ∈ List.filter (fun l => VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing l) (VerinaSpec.lengthOfLIS_postcond.subsequences nums), l.length ≤ result.toNat := by
      intro l hl;
      apply h.right.right;
      constructor;
      · -- By definition of subsequences, every element in the list of subsequences is a sublist of nums.
        have h_subseq : ∀ l ∈ VerinaSpec.lengthOfLIS_postcond.subsequences nums, l.Sublist nums := by
          intro l hl
          have h_subseq_def : ∀ (xs : List ℤ), ∀ l ∈ VerinaSpec.lengthOfLIS_postcond.subsequences xs, l.Sublist xs := by
            intros xs l hl; induction' xs with x xs ih generalizing l <;> simp_all +decide [ VerinaSpec.lengthOfLIS_postcond.subsequences ] ;
            aesop
          exact h_subseq_def nums l hl;
        exact h_subseq l <| List.mem_filter.mp hl |>.1;
      · -- By definition of `isStrictlyIncreasing`, we need to show that for all `i`, if `i + 1 < l.length`, then `l[i]! < l[i + 1]!`.
        have h_strictly_increasing : ∀ l : List ℤ, VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing l → ∀ i : Nat, i + 1 < l.length → l[i]! < l[i + 1]! := by
          intros l hl i hi;
          induction' i with i ih generalizing l;
          · rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide;
            exact ( by rw [ show VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing ( x :: y :: l ) = ( x < y && VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing ( y :: l ) ) by rfl ] at hl; aesop );
          · rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide;
            convert ih ( y :: l ) _ _ using 1;
            · exact?;
            · grind;
        exact h_strictly_increasing l ( List.mem_filter.mp hl |>.2 );
    have h_subseq : sub ∈ List.filter (fun l => VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing l) (VerinaSpec.lengthOfLIS_postcond.subsequences nums) := by
      -- By definition of `subsequences`, `sub` is a subsequence of `nums`.
      have h_subseq_sub : sub ∈ VerinaSpec.lengthOfLIS_postcond.subsequences nums := by
        have h_subseq_sub : ∀ {xs : List ℤ} {sub : List ℤ}, sub.Sublist xs → sub ∈ VerinaSpec.lengthOfLIS_postcond.subsequences xs := by
          -- We can prove this by induction on the list `xs`.
          intro xs sub h_sublist
          induction' xs with x xs ih generalizing sub;
          · cases sub <;> trivial;
          · cases' h_sublist with h_sublist h_sublist;
            · exact List.mem_append_left _ ( ih ‹_› );
            · exact List.mem_append_right _ ( List.mem_map.mpr ⟨ _, ih ‹_›, rfl ⟩ );
        exact h_subseq_sub hsub_inc.1;
      -- Since `sub` is strictly increasing, it satisfies the predicate `isStrictlyIncreasing`.
      have h_subseq_strict : VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing sub := by
        have h_subseq_strict : ∀ i : ℕ, i + 1 < sub.length → sub[i]! < sub[i + 1]! := by
          exact hsub_inc.2;
        have h_subseq_strict : ∀ l : List ℤ, (∀ i : ℕ, i + 1 < l.length → l[i]! < l[i + 1]!) → VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing l = Bool.true := by
          -- By definition of `isStrictlyIncreasing`, if for all i, i + 1 < l.length implies l[i]! < l[i + 1]!, then the list is strictly increasing.
          intros l hl
          induction' l with x l ih;
          · rfl;
          · cases l <;> simp_all +decide [ VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing ];
            exact ⟨ by simpa using hl 0 ( Nat.zero_lt_succ _ ), ih fun i hi => by simpa using hl ( i + 1 ) ( by linarith ) ⟩;
        exact h_subseq_strict sub ‹_›;
      rw [ List.mem_filter ] ; aesop;
    grind