/-
It reveals a misalignment between the problem description and the specification.

The problem description requires the threshold to be a valid floating-point value,
meaning it should never be INF. However, Verina’s pre-condition allows INF as a
valid threshold. Although this weakening is arguably acceptable because it does
not affect the core correctness of the algorithm under typical executions, it
nonetheless introduces a discrepancy between the documented problem constraints
and the formal specification
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bb646c29-e445-4ddb-8b97-f098a56b41f2

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem precondition_equiv (numbers : List Float) (threshold : Float):
  VerinaSpec.has_close_elements_precond numbers threshold ↔ LeetProofSpec.precondition numbers threshold

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

def absDiff (a b : Float) : Float :=
  if a - b < 0.0 then b - a else a - b

def has_close_elements_precond (numbers : List Float) (threshold : Float) : Prop :=
  -- !benchmark @start precond
  threshold ≥ 0.0 ∧
  ¬threshold.isNaN ∧
  numbers.all (fun x => ¬x.isNaN ∧ ¬x.isInf)

-- no NaN or Inf values
  -- !benchmark @end precond

def has_close_elements_postcond (numbers : List Float) (threshold : Float) (result: Bool) (h_precond : has_close_elements_precond (numbers) (threshold)) :=
  -- !benchmark @start postcond
  ¬ result ↔ (List.Pairwise (fun a b => absDiff a b ≥ threshold) numbers)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a Float is valid (not NaN and not infinite)
def isValidFloat (f : Float) : Prop :=
  ¬f.isNaN ∧ ¬f.isInf

-- Helper: Check if all floats in a list are valid
def allValidFloats (numbers : List Float) : Prop :=
  ∀ i, i < numbers.length → isValidFloat numbers[i]!

-- Helper: Check if threshold is valid (non-negative and valid float)
def isValidThreshold (threshold : Float) : Prop :=
  isValidFloat threshold ∧ threshold ≥ 0.0

-- Helper: Absolute difference between two floats
def floatAbsDiff (a : Float) (b : Float) : Float :=
  Float.abs (a - b)

-- Helper: Check if a pair of elements at distinct indices are close
def hasClosePair (numbers : List Float) (threshold : Float) : Prop :=
  ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧
    floatAbsDiff numbers[i]! numbers[j]! < threshold

-- Precondition: threshold is valid and all numbers are valid floats
def precondition (numbers : List Float) (threshold : Float) :=
  isValidThreshold threshold ∧ allValidFloats numbers

-- Postcondition: result is true iff there exists a close pair
def postcondition (numbers : List Float) (threshold : Float) (result : Bool) :=
  result = true ↔ hasClosePair numbers threshold

end LeetProofSpec

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

example : (1.0 / 0.0) ≥ 0.0 ∧ (1.0 / 0.0).isInf := by
  native_decide

theorem counterexample : ∃ (n : List Float) (t : Float), VerinaSpec.has_close_elements_precond n t ∧ ¬ LeetProofSpec.precondition n t := by
  use [ ], 1.0 / 0.0;
  unfold VerinaSpec.has_close_elements_precond LeetProofSpec.precondition;
  unfold LeetProofSpec.isValidThreshold; simp +decide ;
  unfold LeetProofSpec.isValidFloat LeetProofSpec.allValidFloats; norm_num;
  native_decide +revert

end AristotleLemmas

/-
Equivalence theorems
-/
theorem precondition_equiv (numbers : List Float) (threshold : Float):
  VerinaSpec.has_close_elements_precond numbers threshold ↔ LeetProofSpec.precondition numbers threshold := by
  -- Define a counterexample where `numbers = []` and `threshold = 1.0 / 0.0` (infinity).
  set numbers : List Float := []
  set threshold : Float := 1.0 / 0.0;
  have h_precond : VerinaSpec.has_close_elements_precond numbers threshold ∧ ¬ LeetProofSpec.precondition numbers threshold := by sorry;
  have h_equiv : ∀ (numbers : List Float) (threshold : Float), VerinaSpec.has_close_elements_precond numbers threshold ↔ LeetProofSpec.precondition numbers threshold := by
    -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state;
    norm_num +zetaDelta at *;
    constructor;
    sorry;
    · constructor;
      sorry;
      · -- Proof starts here:
        use [ ], 1.0 / 0.0;
        unfold LeetProofSpec.precondition;
        unfold LeetProofSpec.isValidThreshold LeetProofSpec.allValidFloats; norm_num;
        unfold VerinaSpec.has_close_elements_precond LeetProofSpec.isValidFloat; norm_num;
        native_decide +revert;
  sorry

-/
-- Equivalence theorems

theorem precondition_equiv (numbers : List Float) (threshold : Float):
  VerinaSpec.has_close_elements_precond numbers threshold ↔ LeetProofSpec.precondition numbers threshold := by
  sorry

/- Aristotle failed to find a proof. -/
theorem postcondition_equiv (numbers : List Float) (threshold : Float) (result : Bool) (h_precond : VerinaSpec.has_close_elements_precond numbers threshold):
  VerinaSpec.has_close_elements_postcond numbers threshold result h_precond ↔ LeetProofSpec.postcondition numbers threshold result := by
  sorry
