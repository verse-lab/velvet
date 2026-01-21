/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e6dc755e-63ef-4c5f-81a9-93e2dea85c9d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (height : List Nat):
  VerinaSpec.trapRainWater_precond height ↔ LeetProofSpec.precondition height

- theorem postcondition_equiv (height : List Nat) (result : Nat) (h_precond : VerinaSpec.trapRainWater_precond height):
  VerinaSpec.trapRainWater_postcond height result h_precond ↔ LeetProofSpec.postcondition height result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def trapRainWater_precond (height : List Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def trapRainWater_postcond (height : List Nat) (result: Nat) (h_precond : trapRainWater_precond (height)) : Prop :=
  -- !benchmark @start postcond
  let waterAt := List.range height.length |>.map (fun i =>
    let lmax := List.take (i+1) height |>.foldl Nat.max 0
    let rmax := List.drop i height |>.foldl Nat.max 0
    Nat.min lmax rmax - height[i]!)

  result - (waterAt.foldl (· + ·) 0) = 0 ∧ (waterAt.foldl (· + ·) 0) ≤ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: maximum value among positions 0 to i (inclusive) in the list
-- This represents the highest barrier on the left side including position i
def leftMax (height : List Nat) (i : Nat) : Nat :=
  (height.take (i + 1)).foldl max 0

-- Helper: maximum value among positions i to end (inclusive) in the list
-- This represents the highest barrier on the right side including position i
def rightMax (height : List Nat) (i : Nat) : Nat :=
  (height.drop i).foldl max 0

-- Precondition: no special requirements (empty list is valid)
def precondition (height : List Nat) :=
  True

-- Postcondition: result equals the total trapped water
-- Water at each position i is determined by:
--   waterLevel(i) = min(leftMax(i), rightMax(i))
--   trapped(i) = waterLevel(i) - height[i] (if positive, else 0)
-- The result is the sum over all positions
def postcondition (height : List Nat) (result : Nat) :=
  result = (Finset.range height.length).sum (fun i =>
    let waterLevel := min (leftMax height i) (rightMax height i)
    let h := if i < height.length then height[i]! else 0
    if waterLevel > h then waterLevel - h else 0)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (height : List Nat):
  VerinaSpec.trapRainWater_precond height ↔ LeetProofSpec.precondition height := by
  -- Since both preconditions are equivalent to True, they are trivially equivalent to each other.
  simp [VerinaSpec.trapRainWater_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (height : List Nat) (result : Nat) (h_precond : VerinaSpec.trapRainWater_precond height):
  VerinaSpec.trapRainWater_postcond height result h_precond ↔ LeetProofSpec.postcondition height result := by
  -- By definition of `trapRainWater_postcond` and `postcondition`, we can see that they are equivalent because they both calculate the same sum of water trapped at each position.
  simp [VerinaSpec.trapRainWater_postcond, LeetProofSpec.postcondition];
  -- By definition of `List.foldl`, we can rewrite the left-hand side of the equivalence.
  have h_foldl : List.foldl (fun x1 x2 => x1 + x2) 0 (List.map (fun i => (List.foldl Nat.max 0 (List.take (i + 1) height)).min (List.foldl Nat.max 0 (List.drop i height)) - height[i]?.getD 0) (List.range height.length)) = Finset.sum (Finset.range height.length) (fun i => (List.foldl Nat.max 0 (List.take (i + 1) height)).min (List.foldl Nat.max 0 (List.drop i height)) - height[i]?.getD 0) := by
    induction' height.length with n ih <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ];
  simp_all +decide [ Finset.sum_range, List.getElem?_eq_none ];
  simp +decide [ Finset.sum_ite, LeetProofSpec.leftMax, LeetProofSpec.rightMax ];
  simp +decide [ Finset.sum_filter, tsub_eq_zero_iff_le ];
  grind