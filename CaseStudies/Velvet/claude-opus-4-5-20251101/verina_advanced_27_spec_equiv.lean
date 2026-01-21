/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2b83b7ac-9894-470c-8a47-ca64ca45088d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s1 : String) (s2 : String):
  VerinaSpec.longestCommonSubsequence_precond s1 s2 ↔ LeetProofSpec.precondition s1 s2

- theorem postcondition_equiv (s1 : String) (s2 : String) (result : String) (h_precond : VerinaSpec.longestCommonSubsequence_precond s1 s2):
  VerinaSpec.longestCommonSubsequence_postcond s1 s2 result h_precond ↔ LeetProofSpec.postcondition s1 s2 result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def longestCommonSubsequence_precond (s1 : String) (s2 : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

partial def toCharList (s : String) : List Char :=
  s.data

partial def fromCharList (cs : List Char) : String :=
  cs.foldl (fun acc c => acc.push c) ""

partial def lcsAux (xs : List Char) (ys : List Char) : List Char :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' =>
    if x == y then
      x :: lcsAux xs' ys'
    else
      let left  := lcsAux xs' (y :: ys')
      let right := lcsAux (x :: xs') ys'
      if left.length >= right.length then left else right

@[reducible]
def longestCommonSubsequence_postcond (s1 : String) (s2 : String) (result: String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq (arr : List Char) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq s1.toList
  let subseqB := allSubseq s2.toList
  let commonSubseq := subseqA.filter (fun l => subseqB.contains l)
  commonSubseq.contains result.toList ∧ commonSubseq.all (fun l => l.length ≤ result.length)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Check if a string is a subsequence of another string using Mathlib's List.Sublist
def isStringSubseq (sub : String) (s : String) : Prop :=
  sub.toList.Sublist s.toList

-- A string is a common subsequence of two strings if it's a subsequence of both
def isCommonSubseq (sub : String) (s1 : String) (s2 : String) : Prop :=
  isStringSubseq sub s1 ∧ isStringSubseq sub s2

-- Postcondition clauses
-- The result is a subsequence of s1
def ensures1 (s1 : String) (s2 : String) (result : String) :=
  isStringSubseq result s1

-- The result is a subsequence of s2
def ensures2 (s1 : String) (s2 : String) (result : String) :=
  isStringSubseq result s2

-- The result has maximum length among all common subsequences
def ensures3 (s1 : String) (s2 : String) (result : String) :=
  ∀ other : String, isCommonSubseq other s1 s2 → other.length ≤ result.length

def precondition (s1 : String) (s2 : String) :=
  True

-- no preconditions

def postcondition (s1 : String) (s2 : String) (result : String) :=
  ensures1 s1 s2 result ∧
  ensures2 s1 s2 result ∧
  ensures3 s1 s2 result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s1 : String) (s2 : String):
  VerinaSpec.longestCommonSubsequence_precond s1 s2 ↔ LeetProofSpec.precondition s1 s2 := by
  -- Since both preconditions are trivially true, their equivalence is straightforward.
  simp [VerinaSpec.longestCommonSubsequence_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s1 : String) (s2 : String) (result : String) (h_precond : VerinaSpec.longestCommonSubsequence_precond s1 s2):
  VerinaSpec.longestCommonSubsequence_postcond s1 s2 result h_precond ↔ LeetProofSpec.postcondition s1 s2 result := by
  constructor <;> intro h <;> simp +decide [ *, LeetProofSpec.postcondition ] at *;
  · revert h;
    rintro ⟨ h₁, h₂ ⟩;
    refine' ⟨ _, _, _ ⟩;
    · have h_subseq : ∀ (l : List Char), l ∈ List.map List.reverse (List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] s1.toList) → l.Sublist s1.toList := by
        induction' s1.toList using List.reverseRecOn with s1 ih <;> aesop;
      aesop;
    · -- Since the result is in the filtered list, it must be a subsequence of s2.
      have h_subseq_s2 : result.toList ∈ List.map List.reverse ((fun (init : List (List Char)) => List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) init s2.toList) [[]]) := by
        grind;
      -- Since the result is in the list of subsequences of s2, it must be a subsequence of s2.
      have h_subseq_s2 : ∀ {l : List Char}, l ∈ List.map List.reverse ((fun (init : List (List Char)) => List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) init s2.toList) [[]]) → l.Sublist s2.toList := by
        induction' s2.toList using List.reverseRecOn with s2 ih <;> aesop;
      exact h_subseq_s2 ‹_›;
    · intro other h_other
      obtain ⟨h_subseq_s1, h_subseq_s2⟩ := h_other
      have h_subseq_result : other.toList ∈ (List.filter (fun l => ((fun (arr : List Char) => List.map List.reverse ((fun (init : List (List Char)) => List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) init arr) [[]])) s2.toList).contains l) ((fun (arr : List Char) => List.map List.reverse ((fun (init : List (List Char)) => List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) init arr) [[]])) s1.toList)) := by
        have h_subseq_result : other.toList ∈ (fun (arr : List Char) => List.map List.reverse ((fun (init : List (List Char)) => List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) init arr) [[]])) s1.toList := by
          have h_subseq_result : ∀ {l : List Char} {s : List Char}, List.Sublist l s → l ∈ (fun (arr : List Char) => List.map List.reverse ((fun (init : List (List Char)) => List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) init arr) [[]])) s := by
            intros l s h_sublist;
            induction' s with x s ih generalizing l;
            · aesop;
            · rcases h_sublist with ( _ | ⟨ _, _ ⟩ ) <;> simp_all +decide [ List.sublist_cons_iff ];
              · have h_subseq_result : ∀ {l : List Char} {s : List Char}, l ∈ List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) [[]] s → l ∈ List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) [[], [x]] s := by
                  intros l s hl; induction' s using List.reverseRecOn with x s ih generalizing l <;> aesop;
                exact h_subseq_result ( ih ‹_› );
              · have h_subseq_result : ∀ {l : List Char} {s : List Char}, l ∈ List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) [[]] s → l ++ [x] ∈ List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) [[], [x]] s := by
                  intros l s hl; induction' s using List.reverseRecOn with x s ih generalizing l <;> simp_all +decide [ List.foldl ] ;
                  grind;
                exact h_subseq_result ( ih ‹_› );
          exact h_subseq_result h_subseq_s1;
        -- Since `other` is a subsequence of `s2`, its `toList` is contained in the list of all subsequences of `s2`.
        have h_subseq_s2 : other.toList ∈ ((fun (arr : List Char) => List.map List.reverse ((fun (init : List (List Char)) => List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) init arr) [[]])) s2.toList) := by
          have h_subseq_s2 : ∀ {l : List Char} {s : List Char}, l.Sublist s → l ∈ List.map List.reverse ((fun (init : List (List Char)) => List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) init s) [[]]) := by
            intros l s h_subseq; induction' s using List.reverseRecOn with s ih generalizing l; aesop;
            rw [ List.sublist_append_iff ] at h_subseq ; aesop;
          exact h_subseq_s2 ‹_›;
        rw [ List.mem_filter ] ; aesop;
      simp_all +decide [ List.all_eq ];
      simpa using h₂ _ h_subseq_result.1 h_subseq_result.2;
  · -- If the result is a common subsequence and has maximum length, then it must be in the list of common subsequences.
    have h_common_subseq : result.toList ∈ (List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] s1.toList |>.map List.reverse).filter (fun l => (List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] s2.toList |>.map List.reverse).contains l) := by
      -- Since `result` is a common subsequence, it must be in the list of subsequences of `s1` and also in the list of subsequences of `s2`.
      have h_subseq_s1 : result.toList ∈ List.map List.reverse (List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) [[]] s1.toList) := by
        have h_subseq_s1 : ∀ (l : List Char) (sub : List Char), List.Sublist sub l → sub ∈ List.map List.reverse (List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) [[]] l) := by
          intros l sub h_subseq; induction' l using List.reverseRecOn with l ih generalizing sub; aesop;
          rw [ List.sublist_append_iff ] at h_subseq ; aesop;
        exact h_subseq_s1 _ _ h.1
      have h_subseq_s2 : result.toList ∈ List.map List.reverse (List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) [[]] s2.toList) := by
        have h_subseq_s2 : ∀ {l : List Char} {sub : List Char}, List.Sublist sub l → sub ∈ List.map List.reverse (List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) [[]] l) := by
          intros l sub h_subseq; induction' l using List.reverseRecOn with l ih generalizing sub; aesop;
          rw [ List.sublist_append_iff ] at h_subseq ; aesop;
        exact h_subseq_s2 h.2.1;
      rw [ List.mem_filter ] ; aesop;
    have h_max_length : ∀ l ∈ (List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] s1.toList |>.map List.reverse).filter (fun l => (List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] s2.toList |>.map List.reverse).contains l), l.length ≤ result.length := by
      intro l hl;
      apply h.right.right;
      constructor;
      · have h_subseq : ∀ l ∈ List.map List.reverse (List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] s1.toList), l.Sublist s1.toList := by
          induction' s1.toList using List.reverseRecOn with x xs ih <;> aesop;
        exact h_subseq l ( List.mem_filter.mp hl |>.1 );
      · have h_subseq_s2 : ∀ l ∈ (List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] s2.toList |>.map List.reverse), l.Sublist s2.toList := by
          induction' s2.toList using List.reverseRecOn with x xs ih <;> aesop;
        aesop;
    grind