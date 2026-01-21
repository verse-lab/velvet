/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 35fd58c6-0beb-45b0-85cc-c354692401a0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.longestIncreasingSubsequence_precond nums ↔ LeetProofSpec.precondition nums

The following was negated by Aristotle:

- theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.longestIncreasingSubsequence_precond nums):
  VerinaSpec.longestIncreasingSubsequence_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

import Lean
import Mathlib.Tactic
import Mathlib.Data.List.Basic


namespace VerinaSpec

@[reducible]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def longestIncreasingSubsequence_postcond (nums : List Int) (result: Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
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

-- Helper: Check if a list is a valid strictly increasing subsequence of nums
def isIncreasingSubseq (subseq : List Int) (nums : List Int) : Prop :=
  subseq.Sublist nums ∧ isStrictlyIncreasing subseq

-- Precondition: No restrictions on the input list
def precondition (nums : List Int) : Prop :=
  True

-- Postcondition clauses
-- 1. Result does not exceed the length of the input list
def ensures1 (nums : List Int) (result : Int) : Prop :=
  result ≤ nums.length

-- 2. There exists a strictly increasing subsequence with exactly this length
def ensures2 (nums : List Int) (result : Int) : Prop :=
  ∃ subseq : List Int, isIncreasingSubseq subseq nums ∧ subseq.length = result.toNat

-- 3. No strictly increasing subsequence has a greater length
def ensures3 (nums : List Int) (result : Int) : Prop :=
  ∀ subseq : List Int, isIncreasingSubseq subseq nums → subseq.length ≤ result.toNat

def postcondition (nums : List Int) (result : Int) : Prop :=
  ensures1 nums result ∧
  ensures2 nums result ∧
  ensures3 nums result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.longestIncreasingSubsequence_precond nums ↔ LeetProofSpec.precondition nums := by
  exact iff_of_true trivial trivial

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
`verina_fold` computes the set of reversed subsequences of `nums`.
`verina_fold_spec` proves that `s` is in `verina_fold nums` if and only if `s.reverse` is a subsequence of `nums`.
-/
def LeetProofSpec.verina_fold (nums : List Int) : List (List Int) :=
  nums.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]]

theorem LeetProofSpec.verina_fold_spec (nums : List Int) (s : List Int) :
  s ∈ LeetProofSpec.verina_fold nums ↔ s.reverse.Sublist nums := by
  -- We'll use induction on `nums` to prove the equivalence.
  induction' nums using List.reverseRecOn with nums x ih generalizing s;
  · unfold LeetProofSpec.verina_fold; aesop;
  · rw [ LeetProofSpec.verina_fold ] at *;
    simp +zetaDelta at *;
    rw [ List.sublist_append_iff ] at *;
    constructor;
    · rintro ( h | ⟨ a, ha, rfl ⟩ );
      · exact ⟨ s.reverse, [ ], by simp +decide, ih s |>.1 h, by simp +decide ⟩;
      · exact ⟨ a.reverse, [ x ], by simp +decide, ih a |>.1 ha, by simp +decide ⟩;
    · rintro ⟨ l₁, l₂, h₁, h₂, h₃ ⟩;
      rcases l₂ with ( _ | ⟨ _, _ | l₂ ⟩ ) <;> simp_all +decide [ List.sublist_append_iff ]

/-
`verina_allSubseq_spec` shows that mapping reverse over `verina_fold` produces exactly the set of subsequences of `nums`.
-/
theorem LeetProofSpec.verina_allSubseq_spec (nums : List Int) (s : List Int) :
  s ∈ (LeetProofSpec.verina_fold nums).map List.reverse ↔ s.Sublist nums := by
  convert LeetProofSpec.verina_fold_spec nums ( List.reverse s ) using 1;
  · grind;
  · simp +zetaDelta at *

end AristotleLemmas

theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.longestIncreasingSubsequence_precond nums):
  VerinaSpec.longestIncreasingSubsequence_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where `nums` is empty.
  use []
  simp [VerinaSpec.longestIncreasingSubsequence_precond, LeetProofSpec.precondition];
  -- Let's choose `result = -1`.
  use -1;
  -- Let's simplify the goal.
  simp [VerinaSpec.longestIncreasingSubsequence_postcond, LeetProofSpec.postcondition];
  -- Let's simplify the goal. Since we have `ensures1`, `ensures2`, and `ensures3` for the empty list, we can focus on proving them individually.
  simp [LeetProofSpec.ensures1, LeetProofSpec.ensures2, LeetProofSpec.ensures3];
  -- The empty list is a subsequence of any list, and any subsequence of the empty list must be empty.
  simp [LeetProofSpec.isIncreasingSubseq];
  -- The empty list is strictly increasing.
  simp [LeetProofSpec.isStrictlyIncreasing]

-/
theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.longestIncreasingSubsequence_precond nums):
  VerinaSpec.longestIncreasingSubsequence_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  sorry