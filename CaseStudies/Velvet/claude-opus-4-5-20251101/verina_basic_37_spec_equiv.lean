/-
The Verina's post-condition is weak.

This is a very subtle bug. When the input is arr = [] and k = 0, the
post-condition accepts both 0 and −1 as valid results, whereas only −1
is the intended outcome.

This happens because, when result = 0, Verina’s post-condition requires
that

```
(result ≥ 0 →
  arr[result.toNat]! = target ∧
  (∀ i : Nat, i < result.toNat → arr[i]! ≠ target))
```

Since the array is empty, accessing arr[result.toNat]! results in an
out-of-bounds access. In Lean, such an access returns a default value,
namely 0, which accidentally satisfies the post-condition and causes
the incorrect result to be accepted.

The correct condition should be:

```
(result ≥ 0 →
  result.toNat < arr.size ∧
  arr[result.toNat]! = target ∧
  (∀ i : Nat, i < result.toNat → arr[i]! ≠ target))
```
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8f868733-6273-4e0a-90d3-f719bdb61261

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) (target : Int):
  VerinaSpec.findFirstOccurrence_precond arr target ↔ LeetProofSpec.precondition arr target

The following was negated by Aristotle:

- theorem postcondition_equiv (arr : Array Int) (target : Int) (result : Int) (h_precond : VerinaSpec.findFirstOccurrence_precond arr target):
  VerinaSpec.findFirstOccurrence_postcond arr target result h_precond ↔ LeetProofSpec.postcondition arr target result

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

def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList

-- !benchmark @end precond

def findFirstOccurrence_postcond (arr : Array Int) (target : Int) (result: Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :=
  -- !benchmark @start postcond
  (result ≥ 0 →
    arr[result.toNat]! = target ∧
    (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
  (result = -1 →
    (∀ i : Nat, i < arr.size → arr[i]! ≠ target))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper definition: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper definition: check if target exists in the array
def targetExists (arr : Array Int) (target : Int) : Prop :=
  ∃ i : Nat, i < arr.size ∧ arr[i]! = target

-- Precondition: array must be sorted in non-decreasing order
def precondition (arr : Array Int) (target : Int) : Prop :=
  isSortedNonDecreasing arr

-- Postcondition: result is -1 if target not found, otherwise it's the first index
def postcondition (arr : Array Int) (target : Int) (result : Int) : Prop :=
  -- Case 1: target not found, result is -1
  (¬targetExists arr target → result = -1) ∧
  -- Case 2: target found, result is a valid index with the target
  (targetExists arr target →
    result ≥ 0 ∧
    result < arr.size ∧
    arr[result.toNat]! = target ∧
    -- No earlier index contains the target (first occurrence)
    ∀ j : Nat, j < result.toNat → arr[j]! ≠ target)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int) (target : Int):
  VerinaSpec.findFirstOccurrence_precond arr target ↔ LeetProofSpec.precondition arr target := by
  -- The Verina Spec's precond requires the array to be sorted in non-decreasing order, which is exactly what the LeetProofSpec's precondition checks.
  simp [VerinaSpec.findFirstOccurrence_precond, LeetProofSpec.precondition];
  -- The pairwise condition on the list is equivalent to the pairwise condition on the array.
  apply Iff.intro;
  · intro h i j hij hj;
    have := List.pairwise_iff_get.mp h;
    convert this ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij;
    · grind;
    · grind;
  · intro h_sorted;
    rw [ List.pairwise_iff_get ];
    intro i j hij;
    convert h_sorted i j hij ( by simp ) using 1;
    · cases arr ; aesop;
    · simp +decide [ Array.toList ]

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (arr : Array Int) (target : Int) (result : Int) (h_precond : VerinaSpec.findFirstOccurrence_precond arr target):
  VerinaSpec.findFirstOccurrence_postcond arr target result h_precond ↔ LeetProofSpec.postcondition arr target result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where the array is empty.
  use #[];
  -- In this case, the array is empty, so both preconditions are trivially satisfied.
  simp [VerinaSpec.findFirstOccurrence_precond, LeetProofSpec.precondition];
  -- In this case, the array is empty, so the postcondition is trivially satisfied.
  use 0, 0
  simp [VerinaSpec.findFirstOccurrence_postcond, LeetProofSpec.postcondition]

-/
theorem postcondition_equiv (arr : Array Int) (target : Int) (result : Int) (h_precond : VerinaSpec.findFirstOccurrence_precond arr target):
  VerinaSpec.findFirstOccurrence_postcond arr target result h_precond ↔ LeetProofSpec.postcondition arr target result := by
  sorry
