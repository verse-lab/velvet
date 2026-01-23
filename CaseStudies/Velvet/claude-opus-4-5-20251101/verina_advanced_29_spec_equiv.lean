/-
The LeetProof's pre-condition is weak.

The original problem allows empty arrays as input, which is
disallowed by Verina's pre-condition.
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2ede15fe-2ac4-4565-910d-3e851ce037e7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem precondition_equiv (nums : List Nat) (k : Nat):
  VerinaSpec.longestGoodSubarray_precond nums k ↔ LeetProofSpec.precondition nums k

- theorem postcondition_equiv (nums : List Nat) (k : Nat) (result : Nat) (h_precond : VerinaSpec.longestGoodSubarray_precond nums k):
  VerinaSpec.longestGoodSubarray_postcond nums k result h_precond ↔ LeetProofSpec.postcondition nums k result

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
import Std.Data.HashMap


open Std

namespace VerinaSpec

@[reducible]
def longestGoodSubarray_precond (nums : List Nat) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k > 0

-- k must be positive for non-trivial subarrays
  -- !benchmark @end precond

@[reducible]
def longestGoodSubarray_postcond (nums : List Nat) (k : Nat) (result: Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) : Prop :=
  -- !benchmark @start postcond
  let subArrays :=
    List.range (nums.length + 1) |>.flatMap (fun start =>
      List.range (nums.length - start + 1) |>.map (fun len =>
        nums.drop start |>.take len))
  let subArrayFreqs := subArrays.map (fun arr => arr.map (fun x => arr.count x))
  let validSubArrays := subArrayFreqs.filter (fun arr => arr.all (fun x => x ≤ k))

  (nums = [] ∧ result = 0) ∨
  (nums ≠ [] ∧
    validSubArrays.any (fun arr => arr.length = result) ∧
    validSubArrays.all (fun arr => arr.length ≤ result))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: check if a list is "good" (all elements have frequency ≤ k)
def isGoodList (l : List Nat) (k : Nat) : Bool :=
  l.all (fun x => l.count x ≤ k)

-- Helper: extract subarray as a list from index start to index stop (exclusive)
def sublist (l : List Nat) (start : Nat) (stop : Nat) : List Nat :=
  (l.drop start).take (stop - start)

-- Helper: check if there exists a good subarray of a given length
def existsGoodSubarrayOfLength (nums : List Nat) (k : Nat) (len : Nat) : Prop :=
  ∃ start : Nat, start + len ≤ nums.length ∧ isGoodList (sublist nums start (start + len)) k = true

-- Precondition: k must be positive (k > 0) and nums must be non-empty
def precondition (nums : List Nat) (k : Nat) : Prop :=
  k > 0 ∧ nums.length > 0

-- Postcondition: result is the length of the longest good subarray
def postcondition (nums : List Nat) (k : Nat) (result : Nat) : Prop :=
  -- result is a valid length (at least 1, at most nums.length)
  result ≥ 1 ∧
  result ≤ nums.length ∧
  -- there exists a good subarray of length result
  existsGoodSubarrayOfLength nums k result ∧
  -- no good subarray of length greater than result exists
  (∀ len : Nat, len > result → len ≤ nums.length → ¬existsGoodSubarrayOfLength nums k len)

end LeetProofSpec

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Equivalence theorems
-/
theorem precondition_equiv (nums : List Nat) (k : Nat):
  VerinaSpec.longestGoodSubarray_precond nums k ↔ LeetProofSpec.precondition nums k := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case when $k \leq 0$.
  use [];
  -- In this case, the list is empty, so the longest good subarray is also empty.
  use 1; simp [VerinaSpec.longestGoodSubarray_precond, LeetProofSpec.precondition]

-/
-- Equivalence theorems

theorem precondition_equiv (nums : List Nat) (k : Nat):
  VerinaSpec.longestGoodSubarray_precond nums k ↔ LeetProofSpec.precondition nums k := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (nums : List Nat) (k : Nat) (result : Nat) (h_precond : VerinaSpec.longestGoodSubarray_precond nums k):
  VerinaSpec.longestGoodSubarray_postcond nums k result h_precond ↔ LeetProofSpec.postcondition nums k result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where `nums` is empty.
  use [], 1, 0;
  -- In this case, the list is empty, so the longest good subarray has length 0.
  simp [VerinaSpec.longestGoodSubarray_precond, VerinaSpec.longestGoodSubarray_postcond, LeetProofSpec.postcondition]

-/
theorem postcondition_equiv (nums : List Nat) (k : Nat) (result : Nat) (h_precond : VerinaSpec.longestGoodSubarray_precond nums k):
  VerinaSpec.longestGoodSubarray_postcond nums k result h_precond ↔ LeetProofSpec.postcondition nums k result := by
  sorry
