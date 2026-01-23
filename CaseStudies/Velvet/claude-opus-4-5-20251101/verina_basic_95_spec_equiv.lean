/-
Verina's post-condition is weak

The post-condition requires that only the two specified positions are swapped
while all other elements remain unchanged, but it does not enforce that the
length of the array must remain the same. As a result, for the input
`#[1, 2], 0, 1`, both `#[2, 1]` and `#[2, 1, 3]` satisfy the post-condition
and are therefore accepted, even though only one of them reflects the
intended behavior.
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8757ca37-c7e3-4cb2-abe1-3b5a7c4c4d28

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) (i : Int) (j : Int):
  VerinaSpec.swap_precond arr i j ↔ LeetProofSpec.precondition arr i j

The following was negated by Aristotle:

- theorem postcondition_equiv (arr : Array Int) (i : Int) (j : Int) (result : Array Int) (h_precond : VerinaSpec.swap_precond arr i j):
  VerinaSpec.swap_postcond arr i j result h_precond ↔ LeetProofSpec.postcondition arr i j result

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

def swap_precond (arr : Array Int) (i : Int) (j : Int) : Prop :=
  -- !benchmark @start precond
  i ≥ 0 ∧
  j ≥ 0 ∧
  Int.toNat i < arr.size ∧
  Int.toNat j < arr.size

-- !benchmark @end precond

def swap_postcond (arr : Array Int) (i : Int) (j : Int) (result: Array Int) (h_precond : swap_precond (arr) (i) (j)) :=
  -- !benchmark @start postcond
  (result[Int.toNat i]! = arr[Int.toNat j]!) ∧
  (result[Int.toNat j]! = arr[Int.toNat i]!) ∧
  (∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → result[k]! = arr[k]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: indices must be non-negative and within bounds
def precondition (arr : Array Int) (i : Int) (j : Int) :=
  i ≥ 0 ∧ j ≥ 0 ∧ i.toNat < arr.size ∧ j.toNat < arr.size

-- Postcondition: result has same size, elements at i and j are swapped, others unchanged
def postcondition (arr : Array Int) (i : Int) (j : Int) (result : Array Int) :=
  result.size = arr.size ∧
  result[i.toNat]! = arr[j.toNat]! ∧
  result[j.toNat]! = arr[i.toNat]! ∧
  (∀ k : Nat, k < arr.size → k ≠ i.toNat → k ≠ j.toNat → result[k]! = arr[k]!)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int) (i : Int) (j : Int):
  VerinaSpec.swap_precond arr i j ↔ LeetProofSpec.precondition arr i j := by
  rfl

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (arr : Array Int) (i : Int) (j : Int) (result : Array Int) (h_precond : VerinaSpec.swap_precond arr i j):
  VerinaSpec.swap_postcond arr i j result h_precond ↔ LeetProofSpec.postcondition arr i j result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any array `arr` and indices `i` and `j` such that `i ≠ j`.
  use #[1, 2, 3], 0, 1;
  -- Let's choose the result array to be `[2, 1, 3]`.
  use #[2, 1, 3, 4];
  -- Let's choose the result array to be `[2, 1, 3, 4]` and verify the postcondition.
  simp +decide [VerinaSpec.swap_postcond, LeetProofSpec.postcondition];
  -- We need to show that the indices are within the bounds of the array.
  simp [VerinaSpec.swap_precond]

-/
theorem postcondition_equiv (arr : Array Int) (i : Int) (j : Int) (result : Array Int) (h_precond : VerinaSpec.swap_precond arr i j):
  VerinaSpec.swap_postcond arr i j result h_precond ↔ LeetProofSpec.postcondition arr i j result := by
  sorry
