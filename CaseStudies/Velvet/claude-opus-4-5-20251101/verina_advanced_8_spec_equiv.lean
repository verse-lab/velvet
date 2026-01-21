/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 65996b85-ebb7-4215-b87d-8fbe475ecab0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (gas : List Int) (cost : List Int):
  VerinaSpec.canCompleteCircuit_precond gas cost ↔ LeetProofSpec.precondition gas cost

The following was negated by Aristotle:

- theorem postcondition_equiv (gas : List Int) (cost : List Int) (result : Int) (h_precond : VerinaSpec.canCompleteCircuit_precond gas cost):
  VerinaSpec.canCompleteCircuit_postcond gas cost result h_precond ↔ LeetProofSpec.postcondition gas cost result

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
def canCompleteCircuit_precond (gas : List Int) (cost : List Int) : Prop :=
  -- !benchmark @start precond
  gas.length > 0 ∧ gas.length = cost.length

-- !benchmark @end precond

@[reducible]
def canCompleteCircuit_postcond (gas : List Int) (cost : List Int) (result: Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) : Prop :=
  -- !benchmark @start postcond
  let valid (start : Nat) := List.range gas.length |>.all (fun i =>
    let acc := List.range (i + 1) |>.foldl (fun t j =>
      let jdx := (start + j) % gas.length
      t + gas[jdx]! - cost[jdx]!) 0
    acc ≥ 0)
  -- For result = -1: It's impossible to complete the circuit starting from any index
  -- In other words, there's no starting point from which we can always maintain a non-negative gas tank
  (result = -1 → (List.range gas.length).all (fun start => ¬ valid start)) ∧
  -- For result ≥ 0: This is the valid starting point
  -- When starting from this index, the gas tank never becomes negative during the entire circuit
  (result ≥ 0 → result < gas.length ∧ valid result.toNat ∧ (List.range result.toNat).all (fun start => ¬ valid start))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: compute running tank level after visiting k stations starting from station start
-- Returns the tank level after leaving station (start + k - 1) mod n for k > 0
def tankAfterSteps (gas : List Int) (cost : List Int) (start : Nat) (steps : Nat) : Int :=
  match steps with
  | 0 => 0
  | k + 1 =>
    let prev := tankAfterSteps gas cost start k
    let idx := (start + k) % gas.length
    prev + gas[idx]! - cost[idx]!

-- Helper: check if starting from station s allows completing the entire circuit
-- Tank must be non-negative after each step (after refueling and traveling)
def canCompleteFrom (gas : List Int) (cost : List Int) (start : Nat) : Prop :=
  ∀ k : Nat, k < gas.length → tankAfterSteps gas cost start (k + 1) ≥ 0

-- Helper: check if a given index is a valid solution (can complete circuit from there)
def isValidStart (gas : List Int) (cost : List Int) (idx : Nat) : Prop :=
  idx < gas.length ∧ canCompleteFrom gas cost idx

-- Precondition: gas and cost arrays have equal non-zero length
def require1 (gas : List Int) (cost : List Int) :=
  gas.length > 0

def require2 (gas : List Int) (cost : List Int) :=
  gas.length = cost.length

def precondition (gas : List Int) (cost : List Int) :=
  require1 gas cost ∧ require2 gas cost

-- Postcondition: result is -1 if no solution exists, otherwise smallest valid starting index
def ensures1 (gas : List Int) (cost : List Int) (result : Int) :=
  result = -1 ∨ (result ≥ 0 ∧ result < gas.length)

-- If result >= 0, it must be a valid starting station
def ensures2 (gas : List Int) (cost : List Int) (result : Int) :=
  result ≥ 0 → isValidStart gas cost result.toNat

-- If result >= 0, it must be the smallest valid starting station
def ensures3 (gas : List Int) (cost : List Int) (result : Int) :=
  result ≥ 0 → ∀ j : Nat, j < result.toNat → ¬isValidStart gas cost j

-- If result = -1, no valid starting station exists
def ensures4 (gas : List Int) (cost : List Int) (result : Int) :=
  result = -1 → ∀ j : Nat, j < gas.length → ¬canCompleteFrom gas cost j

def postcondition (gas : List Int) (cost : List Int) (result : Int) :=
  ensures1 gas cost result ∧
  ensures2 gas cost result ∧
  ensures3 gas cost result ∧
  ensures4 gas cost result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (gas : List Int) (cost : List Int):
  VerinaSpec.canCompleteCircuit_precond gas cost ↔ LeetProofSpec.precondition gas cost := by
  aesop

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
The foldl accumulation in VerinaSpec is equivalent to the recursive tankAfterSteps in LeetProofSpec.
-/
theorem verina_fold_eq_tank (gas cost : List Int) (start : Nat) (n : Nat) :
  (List.range n).foldl (fun t j => t + gas[(start + j) % gas.length]! - cost[(start + j) % gas.length]!) 0 =
  LeetProofSpec.tankAfterSteps gas cost start n := by
    -- We'll use induction to prove that the foldl operation is equivalent to the recursive definition of `tankAfterSteps`.
    induction' n with n ih;
    · rfl;
    · rw [ List.range_succ, List.foldl_append, ih ];
      exact?

/-
The validity condition in VerinaSpec (using List.all and foldl) is equivalent to canCompleteFrom in LeetProofSpec.
-/
theorem verina_valid_iff_leet_canCompleteFrom (gas cost : List Int) (start : Nat) :
  ((List.range gas.length).all (fun i =>
    let acc := (List.range (i + 1)).foldl (fun t j =>
      let jdx := (start + j) % gas.length
      t + gas[jdx]! - cost[jdx]!) 0
    acc ≥ 0)) ↔
  LeetProofSpec.canCompleteFrom gas cost start := by
    simp [LeetProofSpec.canCompleteFrom];
    congr! 3;
    convert verina_fold_eq_tank gas cost start ( Nat.succ ‹_› ) using 1;
    aesop

end AristotleLemmas

theorem postcondition_equiv (gas : List Int) (cost : List Int) (result : Int) (h_precond : VerinaSpec.canCompleteCircuit_precond gas cost):
  VerinaSpec.canCompleteCircuit_postcond gas cost result h_precond ↔ LeetProofSpec.postcondition gas cost result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose gas = [1, 2, 3] and cost = [3, 2, 1].
  use [1, 2, 3], [3, 2, 1];
  unfold VerinaSpec.canCompleteCircuit_precond VerinaSpec.canCompleteCircuit_postcond LeetProofSpec.postcondition; simp +decide ;
  -- Let's choose `result = -2`.
  use -2; simp +decide [LeetProofSpec.ensures1, LeetProofSpec.ensures2, LeetProofSpec.ensures3, LeetProofSpec.ensures4]

-/
theorem postcondition_equiv (gas : List Int) (cost : List Int) (result : Int) (h_precond : VerinaSpec.canCompleteCircuit_precond gas cost):
  VerinaSpec.canCompleteCircuit_postcond gas cost result h_precond ↔ LeetProofSpec.postcondition gas cost result := by
  sorry