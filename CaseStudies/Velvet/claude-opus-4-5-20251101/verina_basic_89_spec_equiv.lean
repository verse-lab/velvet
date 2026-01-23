/-
The post-condition of LeetProof is weak.

It only requires result to be a sub-sequence of the input array.
However, if the input array contains duplicate elements,
it doesn't enforce that only the first occurrence of each element
is included in the result.
-/


/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dd28735e-40c4-41b7-b83f-9b61f28a4c35

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : List Int):
  VerinaSpec.SetToSeq_precond s ↔ LeetProofSpec.precondition s

The following was negated by Aristotle:

- theorem postcondition_equiv (s : List Int) (result : List Int) (h_precond : VerinaSpec.SetToSeq_precond s):
  VerinaSpec.SetToSeq_postcond s result h_precond ↔ LeetProofSpec.postcondition s result

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

def SetToSeq_precond (s : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def SetToSeq_postcond (s : List Int) (result: List Int) (h_precond : SetToSeq_precond (s)) :=
  -- !benchmark @start postcond
  -- Contains exactly the elements of the set
  result.all (fun a => a ∈ s) ∧ s.all (fun a => a ∈ result) ∧
  -- All elements are unique in the result
  result.all (fun a => result.count a = 1) ∧
  -- The order of elements in the result is preserved
  List.Pairwise (fun a b => (result.idxOf a < result.idxOf b) → (s.idxOf a < s.idxOf b)) result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Postcondition clause 1: Every element in the result appears in the input
def ensures1 (s : List Int) (result : List Int) : Prop :=
  ∀ x, x ∈ result → x ∈ s

-- Postcondition clause 2: Every element in the input appears in the result
def ensures2 (s : List Int) (result : List Int) : Prop :=
  ∀ x, x ∈ s → x ∈ result

-- Postcondition clause 3: The result has no duplicates
def ensures3 (result : List Int) : Prop :=
  result.Nodup

-- Postcondition clause 4: Order preservation - result is a subsequence of s
-- This ensures that the relative order of elements in result matches their order in s
def ensures4 (s : List Int) (result : List Int) : Prop :=
  result.Sublist s

def precondition (s : List Int) : Prop :=
  True

-- no preconditions

def postcondition (s : List Int) (result : List Int) : Prop :=
  ensures1 s result ∧ ensures2 s result ∧ ensures3 result ∧ ensures4 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : List Int):
  VerinaSpec.SetToSeq_precond s ↔ LeetProofSpec.precondition s := by
  exact?

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (s : List Int) (result : List Int) (h_precond : VerinaSpec.SetToSeq_precond s):
  VerinaSpec.SetToSeq_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the specific lists from the provided counterexample.
  use [2, 1, 2, 3], [1, 2, 3];
  -- Let's choose the specific lists from the provided counterexample and verify the conditions.
  simp [LeetProofSpec.postcondition, VerinaSpec.SetToSeq_postcond];
  -- Let's prove the conditions for the given list.
  simp [LeetProofSpec.ensures1, LeetProofSpec.ensures2, LeetProofSpec.ensures3, VerinaSpec.SetToSeq_precond, LeetProofSpec.ensures4]

-/
theorem postcondition_equiv (s : List Int) (result : List Int) (h_precond : VerinaSpec.SetToSeq_precond s):
  VerinaSpec.SetToSeq_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  sorry
