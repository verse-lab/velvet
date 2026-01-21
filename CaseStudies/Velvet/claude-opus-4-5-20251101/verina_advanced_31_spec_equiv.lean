/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 322d5199-ebb7-4cc5-9057-897d7f3fa65d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int):
  VerinaSpec.longestIncreasingSubseqLength_precond xs ↔ LeetProofSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : Nat) (h_precond : VerinaSpec.longestIncreasingSubseqLength_precond xs):
  VerinaSpec.longestIncreasingSubseqLength_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result
-/

import Lean
import Mathlib.Tactic
import Mathlib.Data.List.Basic


namespace VerinaSpec

@[reducible]
def longestIncreasingSubseqLength_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

-- Generate all subsequences
def subsequences {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    let subs := subsequences xs
    subs ++ subs.map (fun s => x :: s)

-- Check if a list is strictly increasing
def isStrictlyIncreasing : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => if x < y then isStrictlyIncreasing (y :: rest) else false

@[reducible]
def longestIncreasingSubseqLength_postcond (xs : List Int) (result: Nat) (h_precond : longestIncreasingSubseqLength_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (xs.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a list is strictly increasing using IsChain from Mathlib
def isStrictlyIncreasing (l : List Int) : Prop :=
  l.IsChain (· < ·)

-- Helper: A list is a valid strictly increasing subsequence of xs
def isIncreasingSubseq (sub : List Int) (xs : List Int) : Prop :=
  List.Sublist sub xs ∧ isStrictlyIncreasing sub

-- Precondition: No restrictions on input
def precondition (xs : List Int) : Prop :=
  True

-- Postcondition:
-- 1. The result is the length of some strictly increasing subsequence of xs
-- 2. No strictly increasing subsequence of xs has length greater than result
-- 3. For empty list, result is 0
def postcondition (xs : List Int) (result : Nat) : Prop :=
  -- There exists a strictly increasing subsequence of length result
  (∃ sub : List Int, isIncreasingSubseq sub xs ∧ sub.length = result) ∧
  -- No strictly increasing subsequence is longer than result
  (∀ sub : List Int, isIncreasingSubseq sub xs → sub.length ≤ result)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (xs : List Int):
  VerinaSpec.longestIncreasingSubseqLength_precond xs ↔ LeetProofSpec.precondition xs := by
  -- Since both preconditions are always true, the equivalence is trivial.
  simp [VerinaSpec.longestIncreasingSubseqLength_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (xs : List Int) (result : Nat) (h_precond : VerinaSpec.longestIncreasingSubseqLength_precond xs):
  VerinaSpec.longestIncreasingSubseqLength_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result := by
  -- By definition of postcondition, we need to show that the two conditions are equivalent.
  simp [VerinaSpec.longestIncreasingSubseqLength_postcond, LeetProofSpec.postcondition];
  unfold LeetProofSpec.isIncreasingSubseq;
  -- The foldl operation generates all possible subsequences of xs, so the two conditions are equivalent.
  have h_foldl_subseq : ∀ (xs : List ℤ), List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] xs = List.map (fun (sub : List ℤ) => List.reverse sub) (List.sublists xs) := by
    intro xs; induction xs using List.reverseRecOn <;> aesop;
  -- Apply the hypothesis `h_foldl_subseq` to rewrite the goal in terms of the sublists of `xs`.
  simp [h_foldl_subseq];
  -- Since `LeetProofSpec.isStrictlyIncreasing` is equivalent to `List.Pairwise (· < ·)`, the two parts of the biconditional are equivalent.
  simp [LeetProofSpec.isStrictlyIncreasing];
  simp +decide [ List.isChain_iff_pairwise ];
  grind