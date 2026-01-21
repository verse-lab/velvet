/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 859cc40b-a626-47eb-88a1-b7b0fe895a47

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem precondition_equiv (N : Nat) (chords : List (List Nat)):
  VerinaSpec.hasChordIntersection_precond N chords ↔ LeetProofSpec.precondition N chords

- theorem postcondition_equiv (N : Nat) (chords : List (List Nat)) (result : Bool) (h_precond : VerinaSpec.hasChordIntersection_precond N chords):
  VerinaSpec.hasChordIntersection_postcond N chords result h_precond ↔ LeetProofSpec.postcondition N chords result

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
def hasChordIntersection_precond (N : Nat) (chords : List (List Nat)) : Prop :=
  -- !benchmark @start precond
  N ≥ 2 ∧
  chords.all (fun chord => chord.length = 2 ∧ chord[0]! ≥ 1 ∧ chord[0]! ≤ 2 * N ∧ chord[1]! ≥ 1 ∧ chord[1]! ≤ 2 * N) ∧
  List.Nodup (chords.flatMap id)

-- !benchmark @end precond

@[reducible]
def hasChordIntersection_postcond (N : Nat) (chords : List (List Nat)) (result: Bool) (h_precond : hasChordIntersection_precond (N) (chords)) : Prop :=
  -- !benchmark @start postcond
  let sortedChords := chords.map (fun chord =>
    let a := chord[0]!
    let b := chord[1]!
    if a > b then [b, a] else [a, b]
  )

  let rec hasIntersection (chord1 : List Nat) (chord2 : List Nat) : Bool :=
    let a1 := chord1[0]!
    let b1 := chord1[1]!
    let a2 := chord2[0]!
    let b2 := chord2[1]!
    (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)

  let rec checkAllPairs (chords : List (List Nat)) : Bool :=
    match chords with
    | [] => false
    | x :: xs =>
      if xs.any (fun y => hasIntersection x y) then true
      else checkAllPairs xs

  ((List.Pairwise (fun x y => !hasIntersection x y) sortedChords) → ¬ result) ∧
  ((sortedChords.any (fun x => chords.any (fun y => hasIntersection x y))) → result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: extract all endpoints from the chord list
def allEndpoints (chords : List (List Nat)) : List Nat :=
  chords.flatten

-- Helper: get endpoint pair from a chord (assumed valid format)
def getChordEndpoints (chord : List Nat) : Nat × Nat :=
  (chord[0]!, chord[1]!)

-- Check if a single chord is valid: exactly 2 distinct elements in range [1, 2N]
def validChord (chord : List Nat) (N : Nat) : Prop :=
  chord.length = 2 ∧
  chord[0]! ≠ chord[1]! ∧
  1 ≤ chord[0]! ∧ chord[0]! ≤ 2 * N ∧
  1 ≤ chord[1]! ∧ chord[1]! ≤ 2 * N

-- Check if all chords are valid
def allChordsValid (chords : List (List Nat)) (N : Nat) : Prop :=
  ∀ chord ∈ chords, validChord chord N

-- Check if all endpoints are distinct
def allEndpointsDistinct (chords : List (List Nat)) : Prop :=
  (allEndpoints chords).Nodup

-- Property-based definition of chord intersection:
-- Two chords (a,b) and (c,d) on a circle with points numbered 1 to 2N clockwise
-- intersect if and only if exactly one of c, d lies strictly between min(a,b) and max(a,b).
-- This linear formula works because points are sequentially labeled around the circle.
def chordsIntersectProp (a : Nat) (b : Nat) (c : Nat) (d : Nat) : Prop :=
  let minAB := min a b
  let maxAB := max a b
  let cBetween := minAB < c ∧ c < maxAB
  let dBetween := minAB < d ∧ d < maxAB
  -- Exactly one of c, d is strictly between min(a,b) and max(a,b)
  (cBetween ∧ ¬dBetween) ∨ (¬cBetween ∧ dBetween)

-- Predicate: there exists a pair of intersecting chords
def existsIntersectingPair (chords : List (List Nat)) : Prop :=
  ∃ i j : Nat, i < chords.length ∧ j < chords.length ∧ i < j ∧
    let chord1 := chords[i]!
    let chord2 := chords[j]!
    let (a, b) := getChordEndpoints chord1
    let (c, d) := getChordEndpoints chord2
    chordsIntersectProp a b c d

def precondition (N : Nat) (chords : List (List Nat)) :=
  N ≥ 2 ∧
  chords.length = N ∧
  allChordsValid chords N ∧
  allEndpointsDistinct chords

def postcondition (N : Nat) (chords : List (List Nat)) (result : Bool) :=
  result = true ↔ existsIntersectingPair chords

end LeetProofSpec

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Equivalence theorems
-/
theorem precondition_equiv (N : Nat) (chords : List (List Nat)):
  VerinaSpec.hasChordIntersection_precond N chords ↔ LeetProofSpec.precondition N chords := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider $N = 3$ and the chords $[[1, 3], [2, 4]]$.
  use 3, [[1, 3], [2, 4]];
  -- Show that the chords $[[1, 3], [2, 4]]$ satisfy the conditions for $N = 3$.
  simp +decide [VerinaSpec.hasChordIntersection_precond, LeetProofSpec.precondition]

-/
-- Equivalence theorems

theorem precondition_equiv (N : Nat) (chords : List (List Nat)):
  VerinaSpec.hasChordIntersection_precond N chords ↔ LeetProofSpec.precondition N chords := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

def test_verina : Bool :=
  let chords := [[3, 1], [4, 2]]
  let sortedChords := chords.map (fun chord =>
    let a := chord[0]!
    let b := chord[1]!
    if a > b then [b, a] else [a, b]
  )
  let hasIntersection (chord1 : List Nat) (chord2 : List Nat) : Bool :=
    let a1 := chord1[0]!
    let b1 := chord1[1]!
    let a2 := chord2[0]!
    let b2 := chord2[1]!
    (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)

  sortedChords.any (fun x => chords.any (fun y => hasIntersection x y))

def test_leet : Bool :=
  let chords := [[3, 1], [4, 2]]
  let c1 := chords[0]!
  let c2 := chords[1]!
  let a := c1[0]!
  let b := c1[1]!
  let c := c2[0]!
  let d := c2[1]!
  let minAB := min a b
  let maxAB := max a b
  let cBetween := minAB < c && c < maxAB
  let dBetween := minAB < d && d < maxAB
  (cBetween && !dBetween) || (!cBetween && dBetween)

#eval test_verina
#eval test_leet

def bad_chords : List (List Nat) := [[3, 1], [4, 2]]

theorem bad_chords_precond : VerinaSpec.hasChordIntersection_precond 2 bad_chords := by
  -- Check that the chords are valid and have distinct endpoints.
  simp [bad_chords, VerinaSpec.hasChordIntersection_precond]

theorem bad_chords_disproof : ¬ (VerinaSpec.hasChordIntersection_postcond 2 bad_chords false bad_chords_precond ↔ LeetProofSpec.postcondition 2 bad_chords false) := by
  unfold VerinaSpec.hasChordIntersection_postcond LeetProofSpec.postcondition;
  unfold LeetProofSpec.existsIntersectingPair;
  simp +decide [ LeetProofSpec.chordsIntersectProp ]

theorem postcondition_equiv_false : ¬ (∀ (N : Nat) (chords : List (List Nat)) (result : Bool) (h_precond : VerinaSpec.hasChordIntersection_precond N chords),
  VerinaSpec.hasChordIntersection_postcond N chords result h_precond ↔ LeetProofSpec.postcondition N chords result) := by
  intro h
  specialize h 2 bad_chords false bad_chords_precond
  exact bad_chords_disproof h

end AristotleLemmas

theorem postcondition_equiv (N : Nat) (chords : List (List Nat)) (result : Bool) (h_precond : VerinaSpec.hasChordIntersection_precond N chords):
  VerinaSpec.hasChordIntersection_postcond N chords result h_precond ↔ LeetProofSpec.postcondition N chords result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any $N$ and $chords$ such that the postcondition is not satisfied.
  use 2, [[3, 1], [4, 2]];
  -- Let's simplify the goal. Since we have already established that the chords intersect, we can focus on the second part of the disjunction.
  simp [VerinaSpec.hasChordIntersection_postcond, LeetProofSpec.postcondition];
  simp +decide [ VerinaSpec.hasChordIntersection_postcond.hasIntersection ];
  exact em _

-/
theorem postcondition_equiv (N : Nat) (chords : List (List Nat)) (result : Bool) (h_precond : VerinaSpec.hasChordIntersection_precond N chords):
  VerinaSpec.hasChordIntersection_postcond N chords result h_precond ↔ LeetProofSpec.postcondition N chords result := by
  sorry