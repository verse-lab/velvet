/-
The Verina's post-condition is weak.

It states that:
1. Any even number occuring in input array should occur in output array
2. Any even number occuring in output array should occur in input array
3. the relative order of elements is preserved, i.e., if x appears before
   y in the input array, then x also appears before y in the output array.

However, this specification fails to account for duplicate elements. For
example, given the input array [2,2], the output [2] still satisfies all
stated post-conditions, even though one occurrence of 2 has been
incorrectly dropped.
-/



/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2b166587-2b49-48aa-a143-f09c3095e9f4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int):
  VerinaSpec.findEvenNumbers_precond arr ↔ LeetProofSpec.precondition arr

The following was negated by Aristotle:

- theorem postcondition_equiv (arr : Array Int) (result : Array Int) (h_precond : VerinaSpec.findEvenNumbers_precond arr):
  VerinaSpec.findEvenNumbers_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result

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

def isEven (n : Int) : Bool :=
  n % 2 = 0

def findEvenNumbers_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : findEvenNumbers_precond (arr)) :=
  -- !benchmark @start postcond
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: check if an integer is even
def isEven (n : Int) : Bool := n % 2 = 0

-- Postcondition clause 1: Every element in result is even
def ensures1 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ i : Nat, i < result.size → isEven (result[i]!) = true

-- Postcondition clause 2: Result is a sublist of the input (preserves order)
def ensures2 (arr : Array Int) (result : Array Int) : Prop :=
  result.toList.Sublist arr.toList

-- Postcondition clause 3: Every even element from input appears in result with same count
def ensures3 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ x : Int, isEven x = true → result.toList.count x = arr.toList.count x

-- Postcondition clause 4: No odd elements in result
def ensures4 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ x : Int, isEven x = false → result.toList.count x = 0

def precondition (arr : Array Int) : Prop :=
  True

-- no preconditions

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  ensures1 arr result ∧
  ensures2 arr result ∧
  ensures3 arr result ∧
  ensures4 arr result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int):
  VerinaSpec.findEvenNumbers_precond arr ↔ LeetProofSpec.precondition arr := by
  exact?

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Counterexample definitions and lemmas showing that VerinaSpec does not imply LeetProofSpec.
ce_arr = [2], ce_res = [2, 2].
ce_verina: VerinaSpec holds for this pair.
ce_leet_fail: LeetProofSpec fails for this pair (count mismatch).
-/
def ce_arr : Array Int := #[2]
def ce_res : Array Int := #[2, 2]

lemma ce_verina : VerinaSpec.findEvenNumbers_postcond ce_arr ce_res True.intro := by
  unfold VerinaSpec.findEvenNumbers_postcond
  constructor
  · intros x hx
    simp [ce_res, ce_arr] at *
    rcases hx with rfl | rfl <;> simp [VerinaSpec.isEven]
  · constructor
    · intros x hx he
      simp [ce_arr, ce_res] at *
      subst hx
      simp
    · intros x y hx hy hex hey hidx
      simp [ce_arr, ce_res] at *
      subst hx hy
      simp

lemma ce_leet_fail : ¬ LeetProofSpec.postcondition ce_arr ce_res := by
  unfold LeetProofSpec.postcondition LeetProofSpec.ensures3
  intro h
  have h3 := h.2.2.1
  specialize h3 2 (by rfl)
  simp [ce_res, ce_arr] at h3

/-
Disproof of the equivalence theorem using the counterexample.
-/
theorem postcondition_equiv_false : ¬ (∀ (arr : Array Int) (result : Array Int) (h_precond : VerinaSpec.findEvenNumbers_precond arr),
  VerinaSpec.findEvenNumbers_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result) := by
    push_neg;
    refine' ⟨ _, _, _, Or.inl ⟨ _, _ ⟩ ⟩;
    exact ce_arr;
    exact ce_res;
    · exact?;
    · exact?;
    · exact?

end AristotleLemmas

theorem postcondition_equiv (arr : Array Int) (result : Array Int) (h_precond : VerinaSpec.findEvenNumbers_precond arr):
  VerinaSpec.findEvenNumbers_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the counterexample arrays `ce_arr` and `ce_res`.
  use ce_arr, ce_res;
  -- Let's choose the counterexample arrays `ce_arr` and `ce_res` and show that the conditions hold.
  use trivial;
  -- Apply the counterexample to derive the contradiction.
  apply Or.inl; exact ⟨ce_verina, ce_leet_fail⟩

-/
theorem postcondition_equiv (arr : Array Int) (result : Array Int) (h_precond : VerinaSpec.findEvenNumbers_precond arr):
  VerinaSpec.findEvenNumbers_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result := by
  sorry
