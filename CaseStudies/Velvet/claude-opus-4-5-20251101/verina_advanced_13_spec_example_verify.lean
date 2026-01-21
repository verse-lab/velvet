import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def allEndpoints (chords : List (List Nat)) : List Nat :=
  chords.flatten

def getChordEndpoints (chord : List Nat) : Nat × Nat :=
  (chord[0]!, chord[1]!)


def validChord (chord : List Nat) (N : Nat) : Prop :=
  chord.length = 2 ∧
  chord[0]! ≠ chord[1]! ∧
  1 ≤ chord[0]! ∧ chord[0]! ≤ 2 * N ∧
  1 ≤ chord[1]! ∧ chord[1]! ≤ 2 * N


def allChordsValid (chords : List (List Nat)) (N : Nat) : Prop :=
  ∀ chord ∈ chords, validChord chord N


def allEndpointsDistinct (chords : List (List Nat)) : Prop :=
  (allEndpoints chords).Nodup





def chordsIntersectProp (a : Nat) (b : Nat) (c : Nat) (d : Nat) : Prop :=
  let minAB := min a b
  let maxAB := max a b
  let cBetween := minAB < c ∧ c < maxAB
  let dBetween := minAB < d ∧ d < maxAB

  (cBetween ∧ ¬dBetween) ∨ (¬cBetween ∧ dBetween)


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


def test1_N : Nat := 3

def test1_chords : List (List Nat) := [[1, 3], [4, 2], [5, 6]]

def test1_Expected : Bool := true

def test2_N : Nat := 3

def test2_chords : List (List Nat) := [[6, 1], [4, 3], [2, 5]]

def test2_Expected : Bool := false

def test5_N : Nat := 2

def test5_chords : List (List Nat) := [[1, 3], [2, 4]]

def test5_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_N test1_chords := by
  unfold precondition test1_N test1_chords
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- N ≥ 2
    decide
  · -- chords.length = N
    native_decide
  · -- allChordsValid chords N
    unfold allChordsValid validChord
    intro chord hchord
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hchord
    rcases hchord with rfl | rfl | rfl
    · native_decide
    · native_decide
    · native_decide
  · -- allEndpointsDistinct chords
    unfold allEndpointsDistinct allEndpoints
    native_decide

theorem test1_postcondition :
  postcondition test1_N test1_chords test1_Expected := by
  simp only [postcondition, test1_N, test1_chords, test1_Expected]
  constructor
  · intro _
    unfold existsIntersectingPair
    refine ⟨0, 1, by decide, by decide, by decide, ?_⟩
    unfold getChordEndpoints chordsIntersectProp
    native_decide
  · intro _
    trivial

theorem test2_precondition : precondition test2_N test2_chords := by
  unfold precondition test2_N test2_chords
  refine ⟨?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · unfold allChordsValid validChord
    intro chord hchord
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hchord
    rcases hchord with rfl | rfl | rfl
    · native_decide
    · native_decide
    · native_decide
  · unfold allEndpointsDistinct allEndpoints
    native_decide

theorem test2_postcondition_0
    (h1 : test2_Expected = false)
    (h2 : True)
    (h3 : True)
    : ¬chordsIntersectProp 6 1 4 3 := by
  unfold chordsIntersectProp
  simp only [min, max, Nat.min_def, Nat.max_def]
  decide

theorem test2_postcondition_1
    (h1 : test2_Expected = false)
    (h4 : ¬chordsIntersectProp 6 1 4 3)
    (h2 : True)
    (h3 : True)
    : ¬chordsIntersectProp 6 1 2 5 := by
  unfold chordsIntersectProp
  simp only [Nat.min_def, Nat.max_def]
  decide

theorem test2_postcondition_2
    (h1 : test2_Expected = false)
    (h4 : ¬chordsIntersectProp 6 1 4 3)
    (h5 : ¬chordsIntersectProp 6 1 2 5)
    (h2 : True)
    (h3 : True)
    : ¬chordsIntersectProp 4 3 2 5 := by
    unfold chordsIntersectProp
    simp only [min, max]
    decide

theorem test2_postcondition_3
    (h1 : test2_Expected = false)
    (h4 : ¬chordsIntersectProp 6 1 4 3)
    (h5 : ¬chordsIntersectProp 6 1 2 5)
    (h6 : ¬chordsIntersectProp 4 3 2 5)
    (h2 : True)
    (h3 : True)
    : ¬existsIntersectingPair test2_chords := by
  intro ⟨i, j, hi, hj, hij, hinter⟩
  simp only [test2_chords, List.length_cons, List.length_nil] at hi hj
  match i, j with
  | 0, 0 => omega
  | 0, 1 => simp only [test2_chords, getChordEndpoints] at hinter; exact h4 hinter
  | 0, 2 => simp only [test2_chords, getChordEndpoints] at hinter; exact h5 hinter
  | 1, 0 => omega
  | 1, 1 => omega
  | 1, 2 => simp only [test2_chords, getChordEndpoints] at hinter; exact h6 hinter
  | 2, 0 => omega
  | 2, 1 => omega
  | 2, 2 => omega
  | i + 3, _ => omega
  | _, j + 3 => omega

theorem test2_postcondition :
  postcondition test2_N test2_chords test2_Expected := by
  -- First, unfold the main definitions to see what we need to prove
  have h1 : test2_Expected = false := by (try simp at *; expose_names); exact rfl; done
  have h2 : (false = true) = False := by (try simp at *; expose_names); exact Bool.false_eq_true; done
  -- The postcondition becomes: false = true ↔ existsIntersectingPair test2_chords
  -- Which simplifies to: False ↔ existsIntersectingPair test2_chords
  -- By false_iff, this is equivalent to: ¬existsIntersectingPair test2_chords
  have h3 : ∀ (p : Prop), (False ↔ p) = ¬p := by (try simp at *; expose_names); exact (fun p ↦ false_iff p); done
  -- Now we need to show no pair of chords intersects
  -- Chord 0 vs Chord 1: [6,1] vs [4,3] - both endpoints of second chord are between 1 and 6
  have h4 : ¬chordsIntersectProp 6 1 4 3 := by (try simp at *; expose_names); exact (test2_postcondition_0 h1 h2 h3); done
  -- Chord 0 vs Chord 2: [6,1] vs [2,5] - both endpoints of second chord are between 1 and 6
  have h5 : ¬chordsIntersectProp 6 1 2 5 := by (try simp at *; expose_names); exact (test2_postcondition_1 h1 h4 h2 h3); done
  -- Chord 1 vs Chord 2: [4,3] vs [2,5] - neither endpoint of second chord is between 3 and 4
  have h6 : ¬chordsIntersectProp 4 3 2 5 := by (try simp at *; expose_names); exact (test2_postcondition_2 h1 h4 h5 h2 h3); done
  -- Since no pair intersects, existsIntersectingPair is false
  have h7 : ¬existsIntersectingPair test2_chords := by (try simp at *; expose_names); exact (test2_postcondition_3 h1 h4 h5 h6 h2 h3); done
  -- Combine to prove the postcondition
  simp only [postcondition, test2_N, test2_chords, test2_Expected]
  constructor
  · intro hfalse
    simp only [Bool.false_eq_true] at hfalse
  · intro hexists
    exact absurd hexists h7

theorem test5_precondition :
  precondition test5_N test5_chords := by
  unfold precondition test5_N test5_chords
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- N ≥ 2
    decide
  · -- chords.length = N
    native_decide
  · -- allChordsValid
    unfold allChordsValid
    intro chord hchord
    simp only [List.mem_cons, List.mem_singleton] at hchord
    cases hchord with
    | inl h =>
      subst h
      unfold validChord
      native_decide
    | inr h =>
      cases h with
      | inl h =>
        subst h
        unfold validChord
        native_decide
      | inr h =>
        simp at h
  · -- allEndpointsDistinct
    unfold allEndpointsDistinct allEndpoints
    native_decide

theorem test5_postcondition :
  postcondition test5_N test5_chords test5_Expected := by
  unfold postcondition test5_Expected test5_chords
  constructor
  · intro _
    unfold existsIntersectingPair
    use 0, 1
    simp only [List.length_cons, List.length_nil]
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    unfold getChordEndpoints chordsIntersectProp
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, List.getElem!_nil]
    left
    constructor
    · constructor <;> native_decide
    · simp only [min, max, Nat.min_def, Nat.max_def]
      native_decide
  · intro _
    rfl

theorem uniqueness (N : Nat) (chords : List (List Nat)):
  precondition N chords →
  (∀ ret1 ret2,
    postcondition N chords ret1 →
    postcondition N chords ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  -- postcondition says: result = true ↔ existsIntersectingPair chords
  unfold postcondition at hpost1 hpost2
  -- hpost1 : ret1 = true ↔ existsIntersectingPair chords
  -- hpost2 : ret2 = true ↔ existsIntersectingPair chords
  -- We need ret1 = ret2
  rw [Bool.eq_iff_iff]
  -- Now we need: (ret1 = true ↔ ret2 = true)
  exact Iff.trans hpost1 hpost2.symm
end Proof
