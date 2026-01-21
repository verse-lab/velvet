/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 32f0e6d4-d3dc-418b-a55a-8a59f8e81bc5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.LongestCommonSubsequence_precond a b ↔ LeetProofSpec.precondition a b

The following was negated by Aristotle:

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Int) (h_precond : VerinaSpec.LongestCommonSubsequence_precond a b):
  VerinaSpec.LongestCommonSubsequence_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result

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


namespace VerinaSpec

def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def intMax (x y : Int) : Int :=
  if x < y then y else x

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

-- A common subsequence is a list that is a sublist of both input lists
def isCommonSubseq (s : List Int) (a : List Int) (b : List Int) : Prop :=
  List.Sublist s a ∧ List.Sublist s b

-- Postcondition clause 1: There exists a common subsequence with the given length
def ensures1 (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  ∃ s : List Int, isCommonSubseq s a.toList b.toList ∧ s.length = result.toNat

-- Postcondition clause 2: No common subsequence is longer than the result
def ensures2 (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  ∀ s : List Int, isCommonSubseq s a.toList b.toList → s.length ≤ result.toNat

-- Postcondition clause 3: Result is bounded by the minimum of array lengths
def ensures3 (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  result.toNat ≤ min a.size b.size

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- No preconditions needed; works for any arrays including empty ones

def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  ensures1 a b result ∧
  ensures2 a b result ∧
  ensures3 a b result

end LeetProofSpec

-- Equivalence theorems

/- Aristotle found this block to be false. Here is a proof of the negation:

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Int) (h_precond : VerinaSpec.LongestCommonSubsequence_precond a b):
  VerinaSpec.LongestCommonSubsequence_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where `a` and `b` are both empty arrays.
  use #[], #[], -1;
  -- In this case, the longest common subsequence is the empty list, so the result should be 0.
  simp [VerinaSpec.LongestCommonSubsequence_postcond, LeetProofSpec.postcondition];
  -- Let's choose the empty list as the common subsequence.
  simp [LeetProofSpec.ensures1, LeetProofSpec.ensures2, VerinaSpec.LongestCommonSubsequence_precond, LeetProofSpec.ensures3];
  -- The empty list is a common subsequence of any two lists.
  simp [LeetProofSpec.isCommonSubseq]

-/
theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Int) (h_precond : VerinaSpec.LongestCommonSubsequence_precond a b):
  VerinaSpec.LongestCommonSubsequence_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  sorry
