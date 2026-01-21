/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5d8db03e-4078-4d59-aec6-95f267e97af7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.minimumRightShifts_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.minimumRightShifts_precond nums):
  VerinaSpec.minimumRightShifts_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result

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

def minimumRightShifts_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  List.Nodup nums

-- !benchmark @end precond

def minimumRightShifts_postcond (nums : List Int) (result: Int) (h_precond : minimumRightShifts_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length

  let isSorted (l : List Int) := List.Pairwise (· ≤ ·) l
  let rightShift (k : Nat) (l : List Int) := l.rotateRight k

  -- specification logic based on the result value
  if n <= 1 then result = 0 else -- specification for base cases

  -- case 1: a non-negative result means a solution was found
  (result ≥ 0 ∧
   -- result corresponds to a valid shift count result < n
   result < n ∧
   -- applying result shifts results in a sorted list
   isSorted (rightShift result.toNat nums) ∧
   -- result is the minimum such non-negative shift count
   (List.range result.toNat |>.all (fun j => ¬ isSorted (rightShift j nums)))
  ) ∨

  -- case 2: result is -1 means no solution exists within n shifts
  (result = -1 ∧
   -- for all possible shift counts k from 0 to n-1, the resulting list is not sorted
   (List.range n |>.all (fun k => ¬ isSorted (rightShift k nums)))
  )

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: perform k right shifts on a list
-- A right shift moves last element to front: [a,b,c,d] -> [d,a,b,c]
-- k right shifts on list of length n is equivalent to List.rotate l (n - k % n) mod n
def rightShift (l : List Int) (k : Nat) : List Int :=
  if l.length = 0 then l
  else
    let effectiveK := k % l.length
    if effectiveK = 0 then l
    else l.rotate (l.length - effectiveK)

-- Helper: check if list is sorted in strictly ascending order
def isStrictlySorted (l : List Int) : Prop :=
  ∀ i : Nat, i + 1 < l.length → l[i]! < l[i + 1]!

-- Helper: check if all elements are distinct
def allDistinct (l : List Int) : Prop :=
  l.Nodup

-- Helper: check if all elements are positive
def allPositive (l : List Int) : Prop :=
  ∀ i : Nat, i < l.length → l[i]! > 0

-- Preconditions
def require1 (nums : List Int) := nums.length > 0

def require2 (nums : List Int) := allDistinct nums

def require3 (nums : List Int) := allPositive nums

def precondition (nums : List Int) :=
  require1 nums ∧ require2 nums ∧ require3 nums

-- Postcondition clauses
-- If result >= 0, then performing result right shifts produces a sorted list
def ensures1 (nums : List Int) (result : Int) :=
  result ≥ 0 → isStrictlySorted (rightShift nums result.toNat)

-- If result >= 0, the result is minimal (no smaller number of shifts works)
def ensures2 (nums : List Int) (result : Int) :=
  result ≥ 0 → ∀ k : Nat, k < result.toNat → ¬isStrictlySorted (rightShift nums k)

-- If result = -1, no number of right shifts can sort the list
-- Since rotations are periodic with period nums.length, we check all possible rotations
def ensures3 (nums : List Int) (result : Int) :=
  result = -1 → ∀ k : Nat, ¬isStrictlySorted (rightShift nums k)

-- Result is either -1 or a valid shift count (0 to n-1)
def ensures4 (nums : List Int) (result : Int) :=
  result = -1 ∨ (result ≥ 0 ∧ result < nums.length)

def postcondition (nums : List Int) (result : Int) :=
  ensures1 nums result ∧
  ensures2 nums result ∧
  ensures3 nums result ∧
  ensures4 nums result

end LeetProofSpec

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Equivalence theorems
-/
theorem precondition_equiv (nums : List Int):
  VerinaSpec.minimumRightShifts_precond nums ↔ LeetProofSpec.precondition nums := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the list [-1, 0].
  use [-1, 0];
  -- Check that the list [-1, 0] satisfies the conditions of `VerinaSpec.minimumRightShifts_precond`.
  simp [VerinaSpec.minimumRightShifts_precond];
  -- Check that the list [-1, 0] does not satisfy the conditions of `LeetProofSpec.precondition`.
  simp [LeetProofSpec.precondition];
  -- Check that the list [-1, 0] does not satisfy the conditions of `LeetProofSpec.require3`.
  simp [LeetProofSpec.require3];
  -- Check that the list [-1, 0] does not satisfy the conditions of `LeetProofSpec.allPositive`.
  simp [LeetProofSpec.allPositive];
  -- Check that the list [-1, 0] does not satisfy the conditions of `LeetProofSpec.allPositive` by showing that there exists an index `x` such that `[-1, 0][x]?.getD 0 ≤ 0`.
  intro h1 h2
  use 1
  simp [h1, h2]

-/
-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.minimumRightShifts_precond nums ↔ LeetProofSpec.precondition nums := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Prove that LeetProofSpec.rightShift is equivalent to List.rotateRight.
-/
lemma LeetProofSpec_rightShift_eq_rotateRight (l : List Int) (k : Nat) :
  LeetProofSpec.rightShift l k = l.rotateRight k := by
  -- By definition of `rightShift`, we split into cases based on the modulo operation.
  cases' n : k % l.length with k' h_mod;
  · unfold LeetProofSpec.rightShift List.rotateRight; aesop;
  · unfold LeetProofSpec.rightShift List.rotateRight;
    split_ifs <;> simp_all +decide [ List.rotate ];
    cases l <;> aesop

/-
Prove that for a list with no duplicates, pairwise less-than-or-equal is equivalent to pairwise strictly-less-than.
-/
lemma pairwise_le_iff_pairwise_lt (l : List Int) (h : l.Nodup) :
  List.Pairwise (· ≤ ·) l ↔ List.Pairwise (· < ·) l := by
  constructor <;> intro h' <;> simp_all +decide [ List.pairwise_iff_get ];
  · intro i j hij; have := h' i j hij; exact lt_of_le_of_ne this ( by intro h'; have := List.nodup_iff_injective_get.mp h; have := @this i j; aesop ) ;
  · exact fun i j hij => le_of_lt ( h' i j hij )

/-
Prove that for a list with no duplicates, being sorted (pairwise <=) is equivalent to being strictly sorted (pairwise <), which matches LeetProofSpec.isStrictlySorted.
-/
lemma sorted_iff_strictlySorted (l : List Int) (h : l.Nodup) :
  List.Pairwise (· ≤ ·) l ↔ LeetProofSpec.isStrictlySorted l := by
    apply Iff.intro;
    · intro hl i hi;
      have := List.pairwise_iff_get.mp hl;
      convert lt_of_le_of_ne ( this ⟨ i, by linarith ⟩ ⟨ i + 1, by linarith ⟩ ( Nat.lt_succ_self _ ) ) _;
      · grind;
      · grind;
      · exact fun h' => by have := List.nodup_iff_injective_get.mp h; have := @this ⟨ i, by linarith ⟩ ⟨ i + 1, by linarith ⟩ ; aesop;
    · intro h'ly_sorted
      have h_le : ∀ i j : ℕ, i < j → i < l.length → j < l.length → l[i]! ≤ l[j]! := by
        -- By induction on $j - i$, we can show that $l[i]! \leq l[j]!$ for any $i < j$.
        intro i j hij hi hj
        induction' hij with j hj ih;
        · exact le_of_lt ( h'ly_sorted i ( by linarith ) );
        · exact le_trans ( ih ( Nat.lt_of_succ_lt hj ) ) ( le_of_lt ( h'ly_sorted _ ( by linarith ) ) );
      rw [ List.pairwise_iff_get ];
      aesop

/-
Prove that LeetProofSpec is unsatisfiable for empty lists, while VerinaSpec is satisfied by 0.
-/
lemma LeetProofSpec_nil_false (result : Int) : ¬ LeetProofSpec.postcondition [] result := by
  rintro ⟨ h1, h2, h3, h4 ⟩;
  cases h4 <;> simp_all +decide [ LeetProofSpec.ensures1, LeetProofSpec.ensures2, LeetProofSpec.ensures3 ];
  · exact h3 0 fun i hi => by contradiction;
  · linarith

lemma VerinaSpec_nil_zero : VerinaSpec.minimumRightShifts_postcond [] 0 (by simp [VerinaSpec.minimumRightShifts_precond]) := by
  -- For the empty list, the only possible shift count is 0, and the postcondition holds.
  simp [VerinaSpec.minimumRightShifts_postcond]

end AristotleLemmas

theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.minimumRightShifts_precond nums):
  VerinaSpec.minimumRightShifts_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any $nums$ such that $nums.length = 0$.
  use []
  use 0
  simp [VerinaSpec.minimumRightShifts_precond, VerinaSpec.minimumRightShifts_postcond];
  -- Apply the lemma that states the postcondition for the empty list is false.
  apply LeetProofSpec_nil_false

-/
theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.minimumRightShifts_precond nums):
  VerinaSpec.minimumRightShifts_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  sorry