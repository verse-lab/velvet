/-
The Verina's post-condition is incorrect.

It fails to properly characterize that a[p] is the first element that is
strictly greater than m.

In particular, the fourth condition,

```
((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!))
```

does not express the intended “first exceeding” semantics. It constrains
a[p] relative to all preceding elements, rather than relative to m and to
the subarray starting at index x.

To make the specification correct, this condition should be replaced by
one that explicitly enforces both strict exceedance and minimality:

```
((p < a.size - 1) →
    (a[p]! > m) ∧
    (∀ i, x ≤ i ∧ i < p → a[p]! ≤ m))
```

-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bc209a01-3b31-48b7-a140-f69b1cffeaf0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (x : Nat):
  VerinaSpec.onlineMax_precond a x ↔ LeetProofSpec.precondition a x

The following was negated by Aristotle:

- theorem postcondition_equiv (a : Array Int) (x : Nat) (result : Int × Nat) (h_precond : VerinaSpec.onlineMax_precond a x):
  VerinaSpec.onlineMax_postcond a x result h_precond ↔ LeetProofSpec.postcondition a x result

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

def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ x > 0 ∧ x < a.size

-- x must be at least 1 (as stated in description)
  -- !benchmark @end precond

def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1

def onlineMax_postcond (a : Array Int) (x : Nat) (result: Int × Nat) (h_precond : onlineMax_precond (a) (x)) :=
  -- !benchmark @start postcond
  let (m, p) := result;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, i < x → a[i]! ≤ m) ∧
  (∃ i, i < x ∧ a[i]! = m) ∧
  ((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!)) ∧
  ((∀ i, x ≤ i → i < a.size → a[i]! ≤ m) → p = a.size - 1)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: check if m is the maximum of the first x elements
def isMaxOfFirstX (a : Array Int) (x : Nat) (m : Int) : Prop :=
  (∃ i : Nat, i < x ∧ a[i]! = m) ∧
  (∀ i : Nat, i < x → a[i]! ≤ m)

-- Helper: check if there exists an element from index x onward that exceeds m
def existsExceedingM (a : Array Int) (x : Nat) (m : Int) : Prop :=
  ∃ i : Nat, x ≤ i ∧ i < a.size ∧ a[i]! > m

-- Helper: p is the first index >= x where a[p] > m
def isFirstExceedingIndex (a : Array Int) (x : Nat) (m : Int) (p : Nat) : Prop :=
  x ≤ p ∧ p < a.size ∧ a[p]! > m ∧ (∀ j : Nat, x ≤ j → j < p → a[j]! ≤ m)

-- Precondition: array is nonempty and x is valid (1 ≤ x < a.size)
def precondition (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ 1 ≤ x ∧ x < a.size

-- Postcondition: m is max of first x elements, p is determined by the ordering condition
def postcondition (a : Array Int) (x : Nat) (result : Int × Nat) : Prop :=
  let m := result.1
  let p := result.2
  -- m is the maximum of the first x elements
  isMaxOfFirstX a x m ∧
  -- p is in valid range [x, a.size)
  x ≤ p ∧ p < a.size ∧
  -- Either p is the first index >= x where a[p] > m, or no such index exists and p = a.size - 1
  ((existsExceedingM a x m ∧ isFirstExceedingIndex a x m p) ∨
   (¬existsExceedingM a x m ∧ p = a.size - 1))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (x : Nat):
  VerinaSpec.onlineMax_precond a x ↔ LeetProofSpec.precondition a x := by
  unfold VerinaSpec.onlineMax_precond LeetProofSpec.precondition;
  grind

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (a : Array Int) (x : Nat) (result : Int × Nat) (h_precond : VerinaSpec.onlineMax_precond a x):
  VerinaSpec.onlineMax_postcond a x result h_precond ↔ LeetProofSpec.postcondition a x result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose a specific array and x value to demonstrate the discrepancy.
  use #[1, 2, 3, 4], 2;
  -- Let's choose the result (2, 3) and verify the conditions.
  use (2, 3);
  unfold VerinaSpec.onlineMax_precond VerinaSpec.onlineMax_postcond LeetProofSpec.postcondition;
  -- Let's choose the result (2, 3) and verify the conditions for the postcondition.
  simp +decide [LeetProofSpec.isMaxOfFirstX, LeetProofSpec.existsExceedingM, LeetProofSpec.isFirstExceedingIndex]

-/
theorem postcondition_equiv (a : Array Int) (x : Nat) (result : Int × Nat) (h_precond : VerinaSpec.onlineMax_precond a x):
  VerinaSpec.onlineMax_postcond a x result h_precond ↔ LeetProofSpec.postcondition a x result := by
  sorry
