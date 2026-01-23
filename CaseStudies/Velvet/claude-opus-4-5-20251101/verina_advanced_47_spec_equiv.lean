/-
Verina's specification is weak.

First, Verina’s precondition is simply True, meaning it imposes
no restrictions on the input. In contrast, for interval problems,
it is standard to require that the start of each interval is less
than or equal to its end.

More importantly, Verina’s postcondition only ensures that each
original interval is covered by some result interval and that the
result intervals do not overlap; it does not require that the set
of points covered by the result exactly matches the set of points
covered by the input intervals.
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9ff72b8d-bffa-481d-8f25-cbbcd160792a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- def precondition_equiv (intervals : List (Prod Int Int)) :
  VerinaSpec.mergeIntervals_precond intervals ↔ LeetProofSpec.precondition intervals

- def postcondition_equiv (intervals : List (Prod Int Int)) (result: List (Prod Int Int)) (h_precond : VerinaSpec.mergeIntervals_precond (intervals)) :
  VerinaSpec.mergeIntervals_postcond intervals result h_precond ↔ LeetProofSpec.postcondition intervals result

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

def mergeIntervals_precond (intervals : List (Prod Int Int)) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def mergeIntervals_postcond (intervals : List (Prod Int Int)) (result: List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) : Prop :=
  -- !benchmark @start postcond
  -- Check that all original intervals are covered by some result interval
  let covered := intervals.all (fun (s, e) =>
    result.any (fun (rs, re) => rs ≤ s ∧ e ≤ re))

  -- Check that no intervals in the result overlap
  let rec noOverlap (l : List (Prod Int Int)) : Bool :=
    match l with
    | [] | [_] => true
    | (_, e1) :: (s2, e2) :: rest => e1 < s2 && noOverlap ((s2, e2) :: rest)

  covered ∧ noOverlap result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- A point x is covered by an interval (a, b) if a ≤ x ≤ b
def pointInInterval (x : Int) (interval : Int × Int) : Prop :=
  interval.1 ≤ x ∧ x ≤ interval.2

-- A point x is covered by a list of intervals if it's in at least one of them
def pointCoveredByList (x : Int) (intervals : List (Int × Int)) : Prop :=
  ∃ interval ∈ intervals, pointInInterval x interval

-- Two intervals are disjoint (non-overlapping) if they don't share any points and don't touch
def intervalsDisjoint (i1 : Int × Int) (i2 : Int × Int) : Prop :=
  i2.1 > i1.2 ∨ i1.1 > i2.2

-- An interval is valid if start ≤ end
def validInterval (interval : Int × Int) : Prop :=
  interval.1 ≤ interval.2

-- All intervals in a list are valid
def allValid (intervals : List (Int × Int)) : Prop :=
  ∀ interval ∈ intervals, validInterval interval

-- The result intervals are pairwise disjoint and separated (no touching)
def pairwiseDisjoint (intervals : List (Int × Int)) : Prop :=
  ∀ i : Nat, ∀ j : Nat, i < intervals.length → j < intervals.length → i ≠ j →
    intervalsDisjoint intervals[i]! intervals[j]!

-- The result is sorted by start times with strict separation
def sortedByStart (intervals : List (Int × Int)) : Prop :=
  ∀ i : Nat, ∀ j : Nat, i < j → j < intervals.length →
    intervals[i]!.2 < intervals[j]!.1

-- Precondition: all input intervals are valid
def precondition (intervals : List (Int × Int)) :=
  allValid intervals

-- Postcondition clauses
-- 1. All result intervals are valid
def ensures1 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  allValid result

-- 2. Coverage preservation: every point covered by input is covered by result
def ensures2 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  ∀ x : Int, pointCoveredByList x intervals → pointCoveredByList x result

-- 3. No extra coverage: every point covered by result is covered by input
def ensures3 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  ∀ x : Int, pointCoveredByList x result → pointCoveredByList x intervals

-- 4. Result intervals are sorted by start time with gaps between them
def ensures4 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  sortedByStart result

-- 5. Result intervals are pairwise disjoint (non-overlapping)
def ensures5 (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  pairwiseDisjoint result

def postcondition (intervals : List (Int × Int)) (result : List (Int × Int)) :=
  ensures1 intervals result ∧
  ensures2 intervals result ∧
  ensures3 intervals result ∧
  ensures4 intervals result ∧
  ensures5 intervals result

end LeetProofSpec

/- Aristotle found this block to be false. Here is a proof of the negation:



def precondition_equiv (intervals : List (Prod Int Int)) :
  VerinaSpec.mergeIntervals_precond intervals ↔ LeetProofSpec.precondition intervals := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any interval $[a, b]$ where $a > b$.
  use [(1, 0)];
  -- By definition of `precondition`, we need to show that `allValid [(1, 0)]` does not hold.
  unfold LeetProofSpec.precondition; simp +decide [LeetProofSpec.allValid];
  -- By definition of `validInterval`, we need to show that `1 ≤ 0` does not hold.
  unfold LeetProofSpec.validInterval; simp +decide [LeetProofSpec.validInterval];
  -- By definition of `mergeIntervals_precond`, we need to show that `True`.
  unfold VerinaSpec.mergeIntervals_precond; simp +decide [VerinaSpec.mergeIntervals_precond]

-/
def precondition_equiv (intervals : List (Prod Int Int)) :
  VerinaSpec.mergeIntervals_precond intervals ↔ LeetProofSpec.precondition intervals := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

theorem postcondition_not_equiv : ¬ (∀ (intervals : List (Int × Int)) (result : List (Int × Int)) (h : VerinaSpec.mergeIntervals_precond intervals), VerinaSpec.mergeIntervals_postcond intervals result h ↔ LeetProofSpec.postcondition intervals result) := by
  push_neg;
  use [ ], [ ( 0, 1 ) ] ; simp +decide [ LeetProofSpec.postcondition ] ;
  unfold LeetProofSpec.ensures1 LeetProofSpec.ensures2 LeetProofSpec.ensures3 LeetProofSpec.ensures4 LeetProofSpec.ensures5;
  simp +decide [ LeetProofSpec.pointCoveredByList ];
  simp +decide [ LeetProofSpec.pointInInterval ];
  simp +decide [ VerinaSpec.mergeIntervals_postcond ];
  exact ⟨ trivial, fun _ h2 _ => absurd ( h2 0 ( by norm_num ) ) ( by norm_num ) ⟩

end AristotleLemmas

def postcondition_equiv (intervals : List (Prod Int Int)) (result: List (Prod Int Int)) (h_precond : VerinaSpec.mergeIntervals_precond (intervals)) :
  VerinaSpec.mergeIntervals_postcond intervals result h_precond ↔ LeetProofSpec.postcondition intervals result := by
  constructor <;> intro h;
  sorry;
  · -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state;
    -- Let's choose specific intervals and result to demonstrate the equivalence.
    use [(1, 3), (2, 4)], [(1, 4)];
    -- Check that the result intervals are pairwise disjoint and sorted by start time with gaps between them.
    simp [VerinaSpec.mergeIntervals_precond, LeetProofSpec.postcondition];
    constructor;
    sorry;
    · simp +decide [ VerinaSpec.mergeIntervals_postcond ];
      -- Wait, there's a mistake. We can actually prove the opposite.
      negate_state;
      -- Proof starts here:
      -- Let's choose any two initial intervals, say $(0, 1)$ and $(1, 2)$.
      aesop

-/
def postcondition_equiv (intervals : List (Prod Int Int)) (result: List (Prod Int Int)) (h_precond : VerinaSpec.mergeIntervals_precond (intervals)) :
  VerinaSpec.mergeIntervals_postcond intervals result h_precond ↔ LeetProofSpec.postcondition intervals result := by
  sorry
