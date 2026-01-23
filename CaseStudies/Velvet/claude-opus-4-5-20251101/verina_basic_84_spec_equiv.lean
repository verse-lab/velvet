/-
Verina's post-condition is weak

The post-condition states that elements less than threshold remain unchanged, but it
does not specify that the length of the array must remain unchanged. As a result, for
the input `#[], 1`, both `#[]` and `#[1]` satisfy the post-condition and are therefore
accepted, even though only one of them reflects the intended behavior.
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 57e44312-da10-4179-b053-56210b5f3466

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) (k : Int):
  VerinaSpec.replace_precond arr k ↔ LeetProofSpec.precondition arr k

The following was negated by Aristotle:

- theorem postcondition_equiv (arr : Array Int) (k : Int) (result : Array Int) (h_precond : VerinaSpec.replace_precond arr k):
  VerinaSpec.replace_postcond arr k result h_precond ↔ LeetProofSpec.postcondition arr k result

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

def replace_precond (arr : Array Int) (k : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def replace_loop (oldArr : Array Int) (k : Int) : Nat → Array Int → Array Int
| i, acc =>
  if i < oldArr.size then
    if (oldArr[i]!) > k then
      replace_loop oldArr k (i+1) (acc.set! i (-1))
    else
      replace_loop oldArr k (i+1) acc
  else
    acc

def replace_postcond (arr : Array Int) (k : Int) (result: Array Int) (h_precond : replace_precond (arr) (k)) :=
  -- !benchmark @start postcond
  (∀ i : Nat, i < arr.size → (arr[i]! > k → result[i]! = -1)) ∧
  (∀ i : Nat, i < arr.size → (arr[i]! ≤ k → result[i]! = arr[i]!))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Postcondition clause 1: result has same size as input
def ensures1 (arr : Array Int) (k : Int) (result : Array Int) :=
  result.size = arr.size

-- Postcondition clause 2: for each index, element is replaced correctly
def ensures2 (arr : Array Int) (k : Int) (result : Array Int) :=
  ∀ i : Nat, i < arr.size →
    (arr[i]! > k → result[i]! = -1) ∧
    (arr[i]! ≤ k → result[i]! = arr[i]!)

def precondition (arr : Array Int) (k : Int) :=
  True

-- no preconditions needed

def postcondition (arr : Array Int) (k : Int) (result : Array Int) :=
  ensures1 arr k result ∧ ensures2 arr k result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int) (k : Int):
  VerinaSpec.replace_precond arr k ↔ LeetProofSpec.precondition arr k := by
  exact?

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (arr : Array Int) (k : Int) (result : Array Int) (h_precond : VerinaSpec.replace_precond arr k):
  VerinaSpec.replace_postcond arr k result h_precond ↔ LeetProofSpec.postcondition arr k result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any arr and k such that arr is empty.
  use #[], 0;
  -- Let's choose any result such that result is not empty.
  use #[1]; simp [VerinaSpec.replace_postcond, LeetProofSpec.postcondition];
  -- Let's simplify the goal.
  simp [VerinaSpec.replace_precond, LeetProofSpec.ensures1, LeetProofSpec.ensures2]

-/
theorem postcondition_equiv (arr : Array Int) (k : Int) (result : Array Int) (h_precond : VerinaSpec.replace_precond arr k):
  VerinaSpec.replace_postcond arr k result h_precond ↔ LeetProofSpec.postcondition arr k result := by
  sorry
