/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d1a49f01-8c1d-4b37-8b7b-d4d90798b17f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (nums : List Int) (target : Int) (result : Prod Nat Nat) (h_precond : VerinaSpec.twoSum_precond nums target):
  VerinaSpec.twoSum_postcond nums target result h_precond ↔ LeetProofSpec.postcondition nums target result

The following was negated by Aristotle:

- theorem precondition_equiv (nums : List Int) (target : Int):
  VerinaSpec.twoSum_precond nums target ↔ LeetProofSpec.precondition nums target

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
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  let pairwiseSum := List.range nums.length |>.flatMap (fun i =>
    nums.drop (i + 1) |>.map (fun y => nums[i]! + y))
  nums.length > 1 ∧ pairwiseSum.count target = 1

-- !benchmark @end precond

def findComplement (nums : List Int) (target : Int) (i : Nat) (x : Int) : Option Nat :=
  let rec aux (nums : List Int) (j : Nat) : Option Nat :=
    match nums with
    | []      => none
    | y :: ys => if x + y = target then some (i + j + 1) else aux ys (j + 1)
  aux nums 0

def twoSumAux (nums : List Int) (target : Int) (i : Nat) : Prod Nat Nat :=
  match nums with
  | []      => panic! "No solution exists"
  | x :: xs =>
    match findComplement xs target i x with
    | some j => (i, j)
    | none   => twoSumAux xs target (i + 1)

@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Prod Nat Nat) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  -- !benchmark @start postcond
  let i := result.fst;
  let j := result.snd;
  (i < j) ∧
  (i < nums.length) ∧ (j < nums.length) ∧
  (nums[i]!) + (nums[j]!) = target

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: There exists exactly one solution (a valid pair of indices)
-- We require that at least one valid pair exists
def hasSolution (nums : List Int) (target : Int) : Prop :=
  ∃ i j : Nat, i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target

def precondition (nums : List Int) (target : Int) : Prop :=
  hasSolution nums target

-- Postcondition clauses
-- The first index is strictly less than the second
def ensures1 (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  result.1 < result.2

-- Both indices are within bounds
def ensures2 (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  result.2 < nums.length

-- The elements at the two indices sum to the target
def ensures3 (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  nums[result.1]! + nums[result.2]! = target

def postcondition (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  ensures1 nums target result ∧
  ensures2 nums target result ∧
  ensures3 nums target result

end LeetProofSpec

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Equivalence theorems
-/
theorem precondition_equiv (nums : List Int) (target : Int):
  VerinaSpec.twoSum_precond nums target ↔ LeetProofSpec.precondition nums target := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the specific example from the provided solution.
  use [2, 2, 1, 3], 3;
  -- Let's simplify the goal.
  simp +decide [VerinaSpec.twoSum_precond, LeetProofSpec.precondition];
  -- We can see that the pair (0, 2) satisfies the condition since 2 + 1 = 3.
  use 0, 2
  simp

-/
-- Equivalence theorems

theorem precondition_equiv (nums : List Int) (target : Int):
  VerinaSpec.twoSum_precond nums target ↔ LeetProofSpec.precondition nums target := by
  sorry

theorem postcondition_equiv (nums : List Int) (target : Int) (result : Prod Nat Nat) (h_precond : VerinaSpec.twoSum_precond nums target):
  VerinaSpec.twoSum_postcond nums target result h_precond ↔ LeetProofSpec.postcondition nums target result := by
  -- By definition of postcondition, we need to show that the result satisfies the conditions for being a valid solution and that the indices are within bounds. We can split the conjunction into its components.
  simp [VerinaSpec.twoSum_postcond, LeetProofSpec.postcondition];
  -- By definition of `ensures1`, `ensures2`, and `ensures3`, we can split the conjunction into its components.
  simp [LeetProofSpec.ensures1, LeetProofSpec.ensures2, LeetProofSpec.ensures3];
  -- If the second component is less than the length of the list, then the first component must also be less than the length.
  intros h1 h2 h3
  exact lt_of_lt_of_le h1 h2.le