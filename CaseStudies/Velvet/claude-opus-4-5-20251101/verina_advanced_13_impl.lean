import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    hasChordIntersection: Determine whether any two chords on a circle intersect
    Natural language breakdown:
    1. We have N chords on a circle, where points are numbered 1 to 2N clockwise
    2. Each chord connects two distinct points on the circle
    3. Two chords intersect inside the circle if and only if their endpoints "interleave"
       in the circular ordering
    4. For chords with endpoints (a, b) and (c, d), they intersect if and only if
       exactly one of c, d lies strictly between min(a,b) and max(a,b)
    5. Since points are labeled 1 to 2N sequentially around the circle, we can use
       a linear min/max approach: chords intersect iff exactly one endpoint of the
       second chord lies in the open interval (min(a,b), max(a,b))
    6. Return true if at least one pair of chords intersects, false otherwise
    7. Preconditions:
       - N >= 2
       - chords has exactly N elements
       - Each chord is a list of exactly 2 elements
       - All endpoints are in range [1, 2N]
       - All 2N endpoints are distinct
-/

section Specs
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
end Specs

section Impl
method hasChordIntersection (N : Nat) (chords : List (List Nat))
  return (result : Bool)
  require precondition N chords
  ensures postcondition N chords result
  do
  let mut found := false
  let mut i := 0
  while i < chords.length
    -- Outer loop invariant: i is bounded
    invariant "i_bounds" 0 ≤ i ∧ i ≤ chords.length
    -- If found is true, there exists an intersecting pair
    invariant "found_implies_exists" found = true → existsIntersectingPair chords
    -- If found is false, no intersecting pair exists among pairs (i', j') where i' < i
    invariant "not_found_implies_no_early" found = false → 
      ¬(∃ i' j' : Nat, i' < i ∧ i' < j' ∧ j' < chords.length ∧
        (let chord1 := chords[i']!
         let chord2 := chords[j']!
         let (a, b) := getChordEndpoints chord1
         let (c, d) := getChordEndpoints chord2
         chordsIntersectProp a b c d))
    done_with i >= chords.length
  do
    let mut j := i + 1
    while j < chords.length
      -- Inner loop invariant: j is bounded
      invariant "j_bounds" i + 1 ≤ j ∧ j ≤ chords.length
      -- i stays in bounds during inner loop
      invariant "i_bounds_inner" 0 ≤ i ∧ i < chords.length
      -- If found is true, there exists an intersecting pair
      invariant "found_implies_exists_inner" found = true → existsIntersectingPair chords
      -- If found is false, no intersecting pair in fully checked rows plus current row up to j
      invariant "not_found_implies_no_early_inner" found = false → 
        ¬(∃ i' j' : Nat, ((i' < i ∧ i' < j' ∧ j' < chords.length) ∨ (i' = i ∧ i + 1 ≤ j' ∧ j' < j)) ∧
          (let chord1 := chords[i']!
           let chord2 := chords[j']!
           let (a, b) := getChordEndpoints chord1
           let (c, d) := getChordEndpoints chord2
           chordsIntersectProp a b c d))
      done_with j >= chords.length
    do
      let chord1 := chords[i]!
      let chord2 := chords[j]!
      let a := chord1[0]!
      let b := chord1[1]!
      let c := chord2[0]!
      let d := chord2[1]!
      let minAB := if a <= b then a else b
      let maxAB := if a >= b then a else b
      let cBetween := minAB < c ∧ c < maxAB
      let dBetween := minAB < d ∧ d < maxAB
      -- Exactly one of c, d is strictly between min(a,b) and max(a,b)
      if (cBetween ∧ ¬dBetween) ∨ (¬cBetween ∧ dBetween) then
        found := true
      j := j + 1
    i := i + 1
  return found
end Impl

section TestCases
-- Test case 1: Example from problem - chords [1,3], [4,2], [5,6] intersect
-- Chord (1,3) and chord (4,2): min=1, max=3, c=4 not between, d=2 between -> intersects
def test1_N : Nat := 3
def test1_chords : List (List Nat) := [[1, 3], [4, 2], [5, 6]]
def test1_Expected : Bool := true

-- Test case 2: No intersections - chords [6,1], [4,3], [2,5]
-- Chord (6,1): min=1, max=6
-- Chord (4,3): min=3, max=4, both in (1,6)
-- Chord (2,5): min=2, max=5, both in (1,6)
-- Checking (6,1) vs (4,3): c=4, d=3, both between 1 and 6 -> no intersection
-- Checking (6,1) vs (2,5): c=2, d=5, both between 1 and 6 -> no intersection
-- Checking (4,3) vs (2,5): min=3, max=4, c=2 not between, d=5 not between -> no intersection
def test2_N : Nat := 3
def test2_chords : List (List Nat) := [[6, 1], [4, 3], [2, 5]]
def test2_Expected : Bool := false

-- Test case 3: Complex case with intersections
-- Chord (2,4) and (3,7): min=2, max=4, c=3 between, d=7 not between -> intersects
def test3_N : Nat := 4
def test3_chords : List (List Nat) := [[2, 4], [3, 7], [8, 6], [5, 1]]
def test3_Expected : Bool := true

-- Test case 4: Two adjacent chords - no intersection
-- Chord (1,2) and (3,4): min=1, max=2, c=3 not between, d=4 not between -> no intersection
def test4_N : Nat := 2
def test4_chords : List (List Nat) := [[1, 2], [3, 4]]
def test4_Expected : Bool := false

-- Test case 5: Two chords that definitely intersect (classic X pattern)
-- Chord (1,3) and chord (2,4): min=1, max=3, c=2 between, d=4 not between -> intersects
def test5_N : Nat := 2
def test5_chords : List (List Nat) := [[1, 3], [2, 4]]
def test5_Expected : Bool := true

-- Test case 6: Two nested chords (no intersection)
-- Chord (1,4) and chord (2,3): min=1, max=4, c=2 between, d=3 between -> no intersection
def test6_N : Nat := 2
def test6_chords : List (List Nat) := [[1, 4], [2, 3]]
def test6_Expected : Bool := false

-- Test case 7: Three chords, all non-intersecting (nested structure)
-- All inner chords have both endpoints inside the outer chord -> no intersections
def test7_N : Nat := 3
def test7_chords : List (List Nat) := [[1, 6], [2, 5], [3, 4]]
def test7_Expected : Bool := false

-- Test case 8: Three chords with intersecting pairs
-- Chord (1,4) and (2,5): min=1, max=4, c=2 between, d=5 not between -> intersects
def test8_N : Nat := 3
def test8_chords : List (List Nat) := [[1, 4], [2, 5], [3, 6]]
def test8_Expected : Bool := true

-- Test case 9: Minimum case with intersection (reversed endpoint order)
-- Chord (1,3) and chord (4,2): min=1, max=3, c=4 not between, d=2 between -> intersects
def test9_N : Nat := 2
def test9_chords : List (List Nat) := [[1, 3], [4, 2]]
def test9_Expected : Bool := true

-- Test case 10: Diametrically opposite chords style (both endpoints inside)
-- Chord (1,4) and chord (2,3): min=1, max=4, both 2 and 3 are between -> no intersection
def test10_N : Nat := 2
def test10_chords : List (List Nat) := [[1, 4], [2, 3]]
def test10_Expected : Bool := false

-- Recommend to validate: 1, 2, 5
end TestCases


section Assertions
-- Test case 1

#assert_same_evaluation #[((hasChordIntersection test1_N test1_chords).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((hasChordIntersection test2_N test2_chords).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((hasChordIntersection test3_N test3_chords).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((hasChordIntersection test4_N test4_chords).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((hasChordIntersection test5_N test5_chords).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((hasChordIntersection test6_N test6_chords).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((hasChordIntersection test7_N test7_chords).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((hasChordIntersection test8_N test8_chords).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((hasChordIntersection test9_N test9_chords).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((hasChordIntersection test10_N test10_chords).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 237, Column 0
-- Message: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
-- 
-- Note: Use `set_option maxHeartbeats <num>` to set the limit.
-- 
-- Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-- Line: prove_postcondition_decidable_for hasChordIntersection
-- [ERROR] Line 237, Column 0
-- Message: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
-- 
-- Note: Use `set_option maxHeartbeats <num>` to set the limit.
-- 
-- Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-- Line: prove_postcondition_decidable_for hasChordIntersection
-- [ERROR] Line 238, Column 0
-- Message: failed to compile definition, compiler IR check failed at `hasChordIntersectionTester`. Error: depends on declaration 'hasChordIntersectionPostDecidable', which has no executable code; consider marking definition as 'noncomputable'
-- Line: derive_tester_for hasChordIntersection
-- [ERROR] Line 239, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do
-- [ERROR] Line 239, Column 0
-- Message: failed to compile definition, compiler IR check failed at `_private.Init.Data.Range.Basic.0.Std.Range.forIn'.loop._at_._private.Init.Data.Range.Basic.0.Std.Range.forIn'.loop._at_._eval.spec_4.spec_4._redArg._lam_0`. Error: depends on declaration 'hasChordIntersectionTester', which has no executable code; consider marking definition as 'noncomputable'
-- Line: run_elab do

-- extract_program_for hasChordIntersection
-- prove_precondition_decidable_for hasChordIntersection
-- prove_postcondition_decidable_for hasChordIntersection
-- derive_tester_for hasChordIntersection
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
--     let arg_1 ← Plausible.SampleableExt.interpSample (List (List Nat))
--     let res := hasChordIntersectionTester arg_0 arg_1
--     pure ((arg_0, arg_1), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct hasChordIntersection by
  -- loom_solve <;> (try simp at *; expose_names)


prove_correct hasChordIntersection by
  loom_solve <;> (try simp at *; expose_names)
end Proof
