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
  pure false

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

