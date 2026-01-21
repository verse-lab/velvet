/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f0dd1319-1e66-4fe0-84a3-e762258e99c3

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.longestConsecutive_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Nat) (h_precond : VerinaSpec.longestConsecutive_precond nums):
  VerinaSpec.longestConsecutive_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic
import Std.Data.HashSet
import Mathlib


open Std

namespace VerinaSpec

def longestConsecutive_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  List.Nodup nums

-- !benchmark @end precond

def isConsecutive (seq : List Int) : Bool :=
  seq.length = 0 ∨ seq.zipIdx.all (fun (x, i) => x = i + seq[0]!)

def longestConsecutive_postcond (nums : List Int) (result: Nat) (h_precond : longestConsecutive_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let sorted_nums := nums.mergeSort
  let consec_sublist_lens := List.range nums.length |>.flatMap (fun start =>
    List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len))) |>.filter isConsecutive |>.map (·.length)

  (nums = [] → result = 0) ∧
  (nums ≠ [] → consec_sublist_lens.contains result ∧ consec_sublist_lens.all (· ≤ result))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if all integers in range [start, start + len) are in the list
def allInRange (nums : List Int) (start : Int) (len : Nat) : Prop :=
  ∀ i : Nat, i < len → (start + i) ∈ nums

-- Helper: Check if a consecutive sequence of given length starting at start exists in the list
def hasConsecutiveSeq (nums : List Int) (start : Int) (len : Nat) : Prop :=
  allInRange nums start len

-- Precondition: The list has no duplicates
def precondition (nums : List Int) : Prop :=
  nums.Nodup

-- Postcondition:
-- 1. If nums is empty, result is 0
-- 2. If nums is non-empty, result is at least 1
-- 3. There exists a consecutive sequence of length result in nums
-- 4. No consecutive sequence of length greater than result exists in nums
def postcondition (nums : List Int) (result : Nat) : Prop :=
  -- Empty list has result 0
  (nums = [] → result = 0) ∧
  -- Non-empty list has result at least 1
  (nums ≠ [] → result ≥ 1) ∧
  -- There exists a starting point where a consecutive sequence of length result exists
  (result > 0 → ∃ start : Int, hasConsecutiveSeq nums start result) ∧
  -- No longer consecutive sequence exists
  (∀ start : Int, ∀ len : Nat, len > result → ¬hasConsecutiveSeq nums start len)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.longestConsecutive_precond nums ↔ LeetProofSpec.precondition nums := by
  exact?

noncomputable section AristotleLemmas

/-
Characterizes `VerinaSpec.isConsecutive` as checking if the list is exactly `[h, h+1, h+2, ...]` where `h` is the first element.
-/
open Std

theorem VerinaSpec.isConsecutive_iff (seq : List Int) :
  VerinaSpec.isConsecutive seq ↔
  seq = (List.range seq.length).map (fun i => (seq.headD 0) + (i : Int)) := by
    -- By definition of `isConsecutive`, we need to show that `seq` is exactly `[h, h+1, h+2, ...]` where `h` is the first element.
    simp [VerinaSpec.isConsecutive];
    constructor <;> intro h;
    · rcases seq <;> simp +decide [ List.zipIdx ] at *;
      induction' ‹List ℤ› using List.reverseRecOn with _ _ ih <;> simp +decide [ List.range_succ ] at *;
      grind;
    · rcases seq <;> simp +decide [ List.range_succ_eq_map ] at *;
      intro a b hab;
      induction' ‹List ℤ› using List.reverseRecOn with _ _ ih <;> simp +decide [ List.range_succ ] at *;
      · aesop;
      · replace h := congr_arg List.reverse h ; simp +decide [ List.reverse_append ] at h;
        grind

/-
If a consecutive sequence is a contiguous sublist of a list, then all elements of that sequence are contained in the list.
-/
open Std

theorem LeetProofSpec.infix_implies_subset (l : List Int) (start : Int) (len : Nat) :
  List.IsInfix ((List.range len).map (fun i => start + (i : Int))) l →
  ∀ i : Nat, i < len → start + i ∈ l := by
    intro h i hi; have := h.subset; aesop;

/-
If a sorted list with no duplicates contains a set of consecutive integers, then those integers must appear as a contiguous sublist.
-/
open Std

theorem LeetProofSpec.subset_implies_infix_of_sorted (l : List Int) (h_sorted : l.Sorted (· ≤ ·)) (h_nodup : l.Nodup) (start : Int) (len : Nat) :
  (∀ i : Nat, i < len → start + i ∈ l) →
  List.IsInfix ((List.range len).map (fun i => start + (i : Int))) l := by
    intro h;
    -- Since `l` is sorted and nodup, it is strictly increasing.
    have h_strict_mono : StrictMonoOn (fun (k : ℕ) => l.get! k) (Finset.range l.length) := by
      intros i hi j hj hij;
      have h_strict_mono : ∀ i j : ℕ, i < j → i < l.length → j < l.length → l.get! i < l.get! j := by
        intros i j hij hi hj;
        have h_strict_mono : ∀ i j : ℕ, i < j → i < l.length → j < l.length → l.get! i < l.get! j := by
          intros i j hij hi hj
          have h_sorted : ∀ i j : ℕ, i < j → i < l.length → j < l.length → l.get! i ≤ l.get! j := by
            intros i j hij hi hj;
            have := List.pairwise_iff_get.mp h_sorted;
            simpa [ hi, hj ] using this ⟨ i, hi ⟩ ⟨ j, hj ⟩ hij
          have h_nodup : ∀ i j : ℕ, i < j → i < l.length → j < l.length → l.get! i ≠ l.get! j := by
            intros i j hij hi hj; have := List.nodup_iff_injective_get.mp h_nodup; have := @this ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; aesop;
          exact?;
        exact h_strict_mono i j hij hi hj;
      exact h_strict_mono i j hij ( Finset.mem_range.mp hi ) ( Finset.mem_range.mp hj );
    -- Let `idx(i)` be the index of `start + i` in `l`.
    obtain ⟨idx, hidx⟩ : ∃ idx : ℕ → ℕ, (∀ i < len, idx i < l.length) ∧ (∀ i < len, l.get! (idx i) = start + i) ∧ StrictMonoOn idx (Finset.range len) := by
      have h_indices : ∀ i < len, ∃ k < l.length, l.get! k = start + i := by
        intro i hi; specialize h i hi; obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp h; use k; aesop;
      choose! idx hidx₁ hidx₂ using h_indices;
      refine' ⟨ idx, hidx₁, hidx₂, fun i hi j hj hij => _ ⟩;
      exact h_strict_mono.lt_iff_lt ( by aesop ) ( by aesop ) |>.1 ( by aesop );
    -- We show by induction that `idx(i) = idx(0) + i`.
    have h_idx_eq : ∀ i < len, idx i = idx 0 + i := by
      intro i hi;
      induction' i with i ih;
      · norm_num;
      · have h_idx_succ : idx (i + 1) ≥ idx i + 1 := by
          exact hidx.2.2 ( Finset.mem_range.mpr ( by linarith ) ) ( Finset.mem_range.mpr ( by linarith ) ) ( by linarith );
        have h_idx_succ : idx (i + 1) ≤ idx i + 1 := by
          by_contra h_contra;
          have h_exists_j : ∃ j, idx i < j ∧ j < idx (i + 1) := by
            exact ⟨ idx i + 1, by linarith, by linarith ⟩;
          obtain ⟨ j, hj₁, hj₂ ⟩ := h_exists_j;
          have h_exists_j : l.get! j ∈ Set.Ioo (l.get! (idx i)) (l.get! (idx (i + 1))) := by
            exact ⟨ h_strict_mono ( show idx i ∈ Finset.range l.length from Finset.mem_range.mpr ( hidx.1 i ( Nat.lt_of_succ_lt hi ) ) ) ( show j ∈ Finset.range l.length from Finset.mem_range.mpr ( by linarith [ hidx.1 ( i + 1 ) hi ] ) ) hj₁, h_strict_mono ( show j ∈ Finset.range l.length from Finset.mem_range.mpr ( by linarith [ hidx.1 ( i + 1 ) hi ] ) ) ( show idx ( i + 1 ) ∈ Finset.range l.length from Finset.mem_range.mpr ( hidx.1 ( i + 1 ) hi ) ) hj₂ ⟩;
          grind;
        linarith [ ih ( Nat.lt_of_succ_lt hi ) ];
    -- Thus `target` is a sublist of `l`.
    have h_sublist : List.map (fun i => l.get! (idx 0 + i)) (List.range len) = List.map (fun i => start + i) (List.range len) := by
      rw [ List.map_congr_left ];
      rotate_right;
      use fun i => start + i;
      · induction ( List.range len ) <;> aesop;
      · exact fun i hi => h_idx_eq i ( List.mem_range.mp hi ) ▸ hidx.2.1 i ( List.mem_range.mp hi );
    rw [ ← h_sublist ];
    have h_sublist : List.map (fun i => l.get! (idx 0 + i)) (List.range len) = List.take len (List.drop (idx 0) l) := by
      refine' List.ext_get _ _ <;> simp +decide [ List.get?_eq_get ];
      · grind;
      · grind;
    rw [h_sublist];
    exact ⟨ List.take ( idx 0 ) l, List.drop ( idx 0 + len ) l, by simp +decide [ List.take_take, List.drop_drop ] ⟩

end AristotleLemmas

theorem postcondition_equiv (nums : List Int) (result : Nat) (h_precond : VerinaSpec.longestConsecutive_precond nums):
  VerinaSpec.longestConsecutive_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  constructor <;> intro h;
  · refine' ⟨ _, _, _, _ ⟩;
    · cases h ; aesop;
    · intro h_nonempty;
      rcases result with ( _ | _ | result ) <;> simp_all +decide [ VerinaSpec.longestConsecutive_postcond ];
      contrapose! h;
      rintro ⟨ a, ha, b, hb, hab ⟩;
      refine' ⟨ 0, _, 1, _, _, _, _ ⟩ <;> norm_num;
      · linarith;
      · linarith;
      · rcases nums with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide [ VerinaSpec.isConsecutive ];
        grind;
      · linarith;
    · -- If result is greater than 0, then there must be a sublist of length result in the sorted list that satisfies isConsecutive.
      intro h_pos
      obtain ⟨start, h_sublist⟩ : ∃ start : ℤ, List.IsInfix ((List.range result).map (fun i => start + (i : ℤ))) (nums.mergeSort) := by
        have := h.2;
        rcases eq_or_ne nums [] <;> simp_all +decide [ List.contains_iff_mem ];
        · cases h ; aesop;
        · obtain ⟨ ⟨ a, ⟨ ⟨ i, hi, j, hj, rfl ⟩, ha ⟩, ha' ⟩, h ⟩ := this;
          rw [ VerinaSpec.isConsecutive_iff ] at ha;
          use (List.take j (List.drop i (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b)))).headD 0;
          rw [ ← ha' ] at *;
          refine' ⟨ List.take i ( nums.mergeSort fun a b => Decidable.decide ( a ≤ b ) ), _, _ ⟩;
          exact List.drop ( i + j ) ( nums.mergeSort fun a b => Decidable.decide ( a ≤ b ) );
          norm_num +zetaDelta at *;
          rw [ ← ha ];
          rw [ ← List.append_assoc, ← List.take_add ];
          rw [ List.take_append_drop ];
      use start;
      intro i hi;
      have h_subset : ∀ x ∈ (List.range result).map (fun i => start + (i : ℤ)), x ∈ nums.mergeSort := by
        exact fun x hx => h_sublist.subset hx;
      aesop;
    · intro start len hlen hseq;
      -- By definition of `hasConsecutiveSeq`, there exists a sublist of `nums.mergeSort` that is consecutive and has length `len`.
      obtain ⟨sublist, hsublist⟩ : ∃ sublist : List ℤ, List.IsInfix sublist (nums.mergeSort) ∧ VerinaSpec.isConsecutive sublist ∧ sublist.length = len := by
        have h_sublist : List.IsInfix ((List.range len).map (fun i => start + (i : ℤ))) (nums.mergeSort) := by
          apply LeetProofSpec.subset_implies_infix_of_sorted;
          · exact?;
          · exact List.Nodup.mergeSort h_precond;
          · aesop;
        refine' ⟨ _, h_sublist, _, _ ⟩ <;> simp +decide [ VerinaSpec.isConsecutive_iff ];
        rcases len with ( _ | _ | len ) <;> simp_all +decide [ List.range_succ_eq_map ];
      have := h.2;
      by_cases h : nums = [] <;> simp_all +decide;
      · grind;
      · contrapose! this;
        rcases hsublist with ⟨ hsublist₁, hsublist₂, hsublist₃ ⟩;
        obtain ⟨ i, hi ⟩ := hsublist₁;
        rcases hi with ⟨ t, ht ⟩ ; use fun _ => ⟨ i.length, by
          replace ht := congr_arg List.length ht ; simp_all +decide;
          linarith, sublist.length, by
          have := congr_arg List.length ht; norm_num at this; omega;, by
          rw [ ← ht ] ; simp +decide [ hsublist₃ ];
          replace ht := congr_arg List.length ht ; simp_all +decide;
          linarith ⟩;
  · unfold VerinaSpec.longestConsecutive_postcond;
    -- Let's unfold the definition of `LeetProofSpec.postcondition`.
    obtain ⟨h_empty, h_nonempty, h_exists, h_max⟩ := h;
    by_cases h : nums = [] <;> simp_all +decide;
    constructor;
    · obtain ⟨ start, hstart ⟩ := h_exists h_nonempty;
      -- By definition of `hasConsecutiveSeq`, the list `[start, start+1, ..., start+result-1]` is a sublist of `nums.mergeSort`.
      have h_sublist : List.IsInfix ((List.range result).map (fun i => start + (i : ℤ))) (nums.mergeSort (fun a b => Decidable.decide (a ≤ b))) := by
        apply LeetProofSpec.subset_implies_infix_of_sorted;
        · exact?;
        · exact?;
        · intro i hi; specialize hstart i hi; aesop;
      obtain ⟨ k, hk ⟩ := h_sublist;
      obtain ⟨ t, ht ⟩ := hk;
      refine' ⟨ _, ⟨ ⟨ k.length, _, _, _, _ ⟩, _ ⟩, _ ⟩;
      exact List.map ( fun i => start + i ) ( List.range result );
      all_goals norm_num [ List.length_map, List.length_range ];
      any_goals exact result;
      · replace ht := congr_arg List.length ht ; simp_all +decide [ List.length_mergeSort ];
        linarith;
      · replace ht := congr_arg List.length ht ; simp_all +decide [ List.length_mergeSort ];
        omega;
      · rw [ ← ht ];
        simp +decide [ List.drop_append, List.take_append ];
      · rw [ VerinaSpec.isConsecutive_iff ];
        rcases result with ( _ | _ | result ) <;> simp_all +decide [ List.range_succ_eq_map ];
        rw [ show List.sum ( List.map ( ( fun a : ℕ => 1 ) ∘ Nat.succ ∘ Nat.succ ) ( List.range result ) ) = result by exact Nat.recOn result ( by norm_num ) fun n ih => by simp +decide [ List.range_succ ] at * ; linarith ];
    · contrapose! h_max;
      obtain ⟨ x, hx, y, hy, hxy ⟩ := h_max;
      -- Since `List.take y (List.drop x (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b)))` is consecutive, it must be of the form `[start, start+1, ..., start+y-1]`.
      obtain ⟨start, hstart⟩ : ∃ start : ℤ, List.take y (List.drop x (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b))) = List.map (fun i => start + i) (List.range y) := by
        have h_consecutive : ∀ {l : List ℤ}, VerinaSpec.isConsecutive l → ∃ start : ℤ, l = List.map (fun i => start + i) (List.range l.length) := by
          intros l hl; use l.headD 0; (
          exact?);
        convert h_consecutive ( show VerinaSpec.isConsecutive _ from by simpa using hxy.1 ) using 1;
        simp +zetaDelta at *;
        rw [ min_eq_left ( by omega ) ];
      refine' ⟨ start, y, hxy.2.1, _ ⟩;
      intro i hi;
      -- Since `List.take y (List.drop x (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b)))` is a sublist of `nums.mergeSort`, and `nums.mergeSort` is a permutation of `nums`, it follows that `start + i` is in `nums`.
      have h_perm : List.Perm (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b)) nums := by
        exact?;
      have h_mem : start + i ∈ List.take y (List.drop x (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b))) := by
        aesop;
      exact h_perm.subset <| List.mem_of_mem_take h_mem |> List.mem_of_mem_drop