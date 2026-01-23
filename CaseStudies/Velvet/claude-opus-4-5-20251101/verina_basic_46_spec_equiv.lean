/-
The Verina's post-condition is weak.

It makes the same mistake as basic_37. When the input is arr = [] and
k = 0, the post-condition accepts both 0 and −1 as valid results, whereas
only −1 is the intended outcome.

This happens because, when result = 0, Verina’s post-condition requires
that

```
(result ≥ 0 →
  arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem))
```

Since the array is empty, accessing arr[result.toNat]! results in an
out-of-bounds access. In Lean, such an access returns a default value,
namely 0, which accidentally satisfies the post-condition and causes
the incorrect result to be accepted.

The correct condition should be:

```
(result ≥ 0 →
  result.toNat < arr.size ∧
  arr[result.toNat]! = elem ∧
  (arr.toList.drop (result.toNat + 1)).all (· ≠ elem))
```
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a3d11495-6f3b-47c6-98f1-7e8361cba0f2

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) (elem : Int):
  VerinaSpec.lastPosition_precond arr elem ↔ LeetProofSpec.precondition arr elem

The following was negated by Aristotle:

- theorem postcondition_equiv (arr : Array Int) (elem : Int) (result : Int) (h_precond : VerinaSpec.lastPosition_precond arr elem):
  VerinaSpec.lastPosition_postcond arr elem result h_precond ↔ LeetProofSpec.postcondition arr elem result

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

def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList

-- !benchmark @end precond

def lastPosition_postcond (arr : Array Int) (elem : Int) (result: Int) (h_precond : lastPosition_precond (arr) (elem)) :=
  -- !benchmark @start postcond
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper definition: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition: array must be sorted in non-decreasing order
def precondition (arr : Array Int) (elem : Int) :=
  isSortedNonDecreasing arr

-- Postcondition clauses
-- Case 1: Element found - result is the last index where elem appears
def ensures_found (arr : Array Int) (elem : Int) (result : Int) :=
  result ≥ 0 →
    (result.toNat < arr.size ∧
     arr[result.toNat]! = elem ∧
     (∀ k : Nat, k < arr.size → k > result.toNat → arr[k]! ≠ elem))

-- Case 2: Element not found - result is -1 and elem does not appear in array
def ensures_not_found (arr : Array Int) (elem : Int) (result : Int) :=
  result = -1 →
    (∀ k : Nat, k < arr.size → arr[k]! ≠ elem)

-- Case 3: Result is either -1 or a valid non-negative index
def ensures_valid_result (arr : Array Int) (elem : Int) (result : Int) :=
  result = -1 ∨ (result ≥ 0 ∧ result.toNat < arr.size)

-- Case 4: If elem exists in the array, result must be non-negative
def ensures_completeness (arr : Array Int) (elem : Int) (result : Int) :=
  (∃ k : Nat, k < arr.size ∧ arr[k]! = elem) → result ≥ 0

def postcondition (arr : Array Int) (elem : Int) (result : Int) :=
  ensures_found arr elem result ∧
  ensures_not_found arr elem result ∧
  ensures_valid_result arr elem result ∧
  ensures_completeness arr elem result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int) (elem : Int):
  VerinaSpec.lastPosition_precond arr elem ↔ LeetProofSpec.precondition arr elem := by
  -- To prove the equivalence, we can use the fact that the pairwise condition on the array is equivalent to the isSortedNonDecreasing condition.
  apply Iff.intro;
  · intro h i j hij hj;
    have := List.pairwise_iff_get.mp h;
    convert this ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij;
    · grind;
    · grind;
  · intro h;
    unfold VerinaSpec.lastPosition_precond;
    rw [ List.pairwise_iff_get ];
    intro i j hij; have := h ( i : ℕ ) ( j : ℕ ) ; aesop;

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (arr : Array Int) (elem : Int) (result : Int) (h_precond : VerinaSpec.lastPosition_precond arr elem):
  VerinaSpec.lastPosition_postcond arr elem result h_precond ↔ LeetProofSpec.postcondition arr elem result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where the array is empty.
  use #[];
  -- Consider the case where the array is empty and the element is 0.
  use 0, 0;
  -- In this case, the array is empty, so the last position of 0 is -1.
  simp [VerinaSpec.lastPosition_precond, VerinaSpec.lastPosition_postcond, LeetProofSpec.postcondition];
  -- In this case, the array is empty, so the result must be -1.
  simp [LeetProofSpec.ensures_found, LeetProofSpec.ensures_not_found, LeetProofSpec.ensures_valid_result, LeetProofSpec.ensures_completeness]

-/
theorem postcondition_equiv (arr : Array Int) (elem : Int) (result : Int) (h_precond : VerinaSpec.lastPosition_precond arr elem):
  VerinaSpec.lastPosition_postcond arr elem result h_precond ↔ LeetProofSpec.postcondition arr elem result := by
  sorry
