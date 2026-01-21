import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def ensures1 (a : Int) (b : Int) (c : Int) (result : Int) :=
  result ≥ a ∧ result ≥ b ∧ result ≥ c


def ensures2 (a : Int) (b : Int) (c : Int) (result : Int) :=
  result = a ∨ result = b ∨ result = c

def precondition (a : Int) (b : Int) (c : Int) :=
  True

def postcondition (a : Int) (b : Int) (c : Int) (result : Int) :=
  ensures1 a b c result ∧
  ensures2 a b c result


def test1_a : Int := 3

def test1_b : Int := 2

def test1_c : Int := 1

def test1_Expected : Int := 3

def test3_a : Int := 10

def test3_b : Int := 20

def test3_c : Int := 15

def test3_Expected : Int := 20

def test4_a : Int := -1

def test4_b : Int := -2

def test4_c : Int := -3

def test4_Expected : Int := -1







section Proof
theorem test1_precondition :
  precondition test1_a test1_b test1_c := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_b test1_c test1_Expected := by
  unfold postcondition ensures1 ensures2 test1_a test1_b test1_c test1_Expected
  constructor
  · constructor
    · decide
    · constructor
      · decide
      · decide
  · left
    rfl

theorem test3_precondition :
  precondition test3_a test3_b test3_c := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_a test3_b test3_c test3_Expected := by
  unfold postcondition ensures1 ensures2 test3_a test3_b test3_c test3_Expected
  constructor
  · constructor
    · decide
    · constructor
      · decide
      · decide
  · right
    left
    rfl

theorem test4_precondition :
  precondition test4_a test4_b test4_c := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_a test4_b test4_c test4_Expected := by
  unfold postcondition ensures1 ensures2 test4_a test4_b test4_c test4_Expected
  constructor
  · constructor
    · decide
    · constructor
      · decide
      · decide
  · left
    rfl

theorem uniqueness (a : Int) (b : Int) (c : Int):
  precondition a b c →
  (∀ ret1 ret2,
    postcondition a b c ret1 →
    postcondition a b c ret2 →
    ret1 = ret2) := by
  intro _
  intro ret1 ret2 h1 h2
  unfold postcondition ensures1 ensures2 at h1 h2
  obtain ⟨⟨h1_ge_a, h1_ge_b, h1_ge_c⟩, h1_eq⟩ := h1
  obtain ⟨⟨h2_ge_a, h2_ge_b, h2_ge_c⟩, h2_eq⟩ := h2
  -- Show ret2 ≥ ret1 by case analysis on h1_eq
  have le1 : ret1 ≤ ret2 := by
    rcases h1_eq with h1a | h1b | h1c
    · -- ret1 = a
      rw [h1a]
      exact h2_ge_a
    · -- ret1 = b
      rw [h1b]
      exact h2_ge_b
    · -- ret1 = c
      rw [h1c]
      exact h2_ge_c
  -- Show ret1 ≥ ret2 by case analysis on h2_eq
  have le2 : ret2 ≤ ret1 := by
    rcases h2_eq with h2a | h2b | h2c
    · -- ret2 = a
      rw [h2a]
      exact h1_ge_a
    · -- ret2 = b
      rw [h2b]
      exact h1_ge_b
    · -- ret2 = c
      rw [h2c]
      exact h1_ge_c
  -- Apply antisymmetry
  exact Int.le_antisymm le1 le2
end Proof
