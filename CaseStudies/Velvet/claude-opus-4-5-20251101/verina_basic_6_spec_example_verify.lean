import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (a : Int) (b : Int) (c : Int) : Prop :=
  True



def ensures1 (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  result ≤ a ∧ result ≤ b ∧ result ≤ c


def ensures2 (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  result = a ∨ result = b ∨ result = c

def postcondition (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  ensures1 a b c result ∧ ensures2 a b c result


def test1_a : Int := 3

def test1_b : Int := 2

def test1_c : Int := 1

def test1_Expected : Int := 1

def test4_a : Int := -1

def test4_b : Int := 2

def test4_c : Int := 3

def test4_Expected : Int := -1

def test9_a : Int := -5

def test9_b : Int := -2

def test9_c : Int := -3

def test9_Expected : Int := -5







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
  · right
    right
    rfl

theorem test4_precondition :
  precondition test4_a test4_b test4_c := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_a test4_b test4_c test4_Expected := by
  unfold postcondition ensures1 ensures2 test4_a test4_b test4_c test4_Expected
  native_decide

theorem test9_precondition :
  precondition test9_a test9_b test9_c := by
  intros; expose_names; exact (trivial); done

theorem test9_postcondition :
  postcondition test9_a test9_b test9_c test9_Expected := by
  unfold postcondition ensures1 ensures2 test9_a test9_b test9_c test9_Expected
  constructor
  · constructor
    · native_decide
    · constructor
      · native_decide
      · native_decide
  · left
    rfl

theorem uniqueness (a : Int) (b : Int) (c : Int):
  precondition a b c →
  (∀ ret1 ret2,
    postcondition a b c ret1 →
    postcondition a b c ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- Extract components from postconditions
  unfold postcondition at hpost1 hpost2
  unfold ensures1 at hpost1 hpost2
  unfold ensures2 at hpost1 hpost2
  obtain ⟨⟨h1a, h1b, h1c⟩, h1eq⟩ := hpost1
  obtain ⟨⟨h2a, h2b, h2c⟩, h2eq⟩ := hpost2
  -- Prove ret1 ≤ ret2 by case analysis on h2eq
  have hle1 : ret1 ≤ ret2 := by
    cases h2eq with
    | inl h => rw [h]; exact h1a
    | inr h => 
      cases h with
      | inl h => rw [h]; exact h1b
      | inr h => rw [h]; exact h1c
  -- Prove ret2 ≤ ret1 by case analysis on h1eq
  have hle2 : ret2 ≤ ret1 := by
    cases h1eq with
    | inl h => rw [h]; exact h2a
    | inr h => 
      cases h with
      | inl h => rw [h]; exact h2b
      | inr h => rw [h]; exact h2c
  -- Apply antisymmetry
  exact Int.le_antisymm hle1 hle2
end Proof
