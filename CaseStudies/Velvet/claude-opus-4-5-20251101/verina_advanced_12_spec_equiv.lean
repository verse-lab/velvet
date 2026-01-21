/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 53363283-1d99-4a75-98b6-4d6070752aa4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Int):
  VerinaSpec.firstDuplicate_precond lst ↔ LeetProofSpec.precondition lst

The following was negated by Aristotle:

- theorem postcondition_equiv (lst : List Int) (result : Option Int) (h_precond : VerinaSpec.firstDuplicate_precond lst):
  VerinaSpec.firstDuplicate_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result

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

@[reducible]
def firstDuplicate_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def firstDuplicate_postcond (lst : List Int) (result: Option Int) (h_precond : firstDuplicate_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  match result with
  | none => List.Nodup lst
  | some x =>
    lst.count x > 1 ∧
    (lst.filter (fun y => lst.count y > 1)).head? = some x

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if element at index j appeared in the prefix lst[0..j-1]
-- Using List.take and List.contains as suggested by LeanExplore

-- Postcondition: Characterize the first duplicate
-- When result is some x:
--   - There exists an index j where lst[j]! = x and x appears in lst[0..j-1]
--   - j is the smallest such index (no earlier index has this property)
-- When result is none:
--   - No element appears twice (no index j has lst[j]! in its prefix)

def precondition (lst : List Int) :=
  True

-- no preconditions

def postcondition (lst : List Int) (result : Option Int) :=
  match result with
  | none =>
      -- No element appears in its prefix (no duplicates)
      ∀ j : Nat, j < lst.length → ¬((lst.take j).contains lst[j]!)
  | some x =>
      -- There exists a position j where:
      -- 1. lst[j]! = x
      -- 2. x appears in the prefix lst[0..j-1]
      -- 3. j is minimal (no earlier position has an element appearing in its prefix)
      ∃ j : Nat, j < lst.length ∧
                 lst[j]! = x ∧
                 (lst.take j).contains x ∧
                 (∀ k : Nat, k < j → ¬((lst.take k).contains lst[k]!))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (lst : List Int):
  VerinaSpec.firstDuplicate_precond lst ↔ LeetProofSpec.precondition lst := by
  exact Iff.rfl

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
The postconditions are not equivalent. A counterexample is [2, 1, 3, 5, 3, 2], where VerinaSpec selects 2 (first occurrence of a duplicate) while LeetProofSpec selects 3 (first second-occurrence).
-/
def counterexample : List Int := [2, 1, 3, 5, 3, 2]

theorem postcondition_not_equiv : ¬ (∀ (lst : List Int) (result : Option Int) (h : VerinaSpec.firstDuplicate_precond lst), VerinaSpec.firstDuplicate_postcond lst result h ↔ LeetProofSpec.postcondition lst result) := by
  simp +zetaDelta at *;
  -- Consider the list [2, 1, 3, 5, 3, 2]
  use [2, 1, 3, 5, 3, 2];
  use some 2; simp +decide [ VerinaSpec.firstDuplicate_postcond, LeetProofSpec.postcondition ] ;

end AristotleLemmas

theorem postcondition_equiv (lst : List Int) (result : Option Int) (h_precond : VerinaSpec.firstDuplicate_precond lst):
  VerinaSpec.firstDuplicate_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the specific list and result from the counterexample.
  use counterexample, some 2;
  -- Let's verify the postcondition for the counterexample.
  simp [VerinaSpec.firstDuplicate_postcond, LeetProofSpec.postcondition];
  -- Let's simplify the goal.
  simp (config := { decide := true }) only [List.count]

-/
theorem postcondition_equiv (lst : List Int) (result : Option Int) (h_precond : VerinaSpec.firstDuplicate_precond lst):
  VerinaSpec.firstDuplicate_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result := by
  sorry
