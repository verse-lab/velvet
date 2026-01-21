import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (a : Int) (b : Int) :=
  True




def postcondition (a : Int) (b : Int) (result : Bool) :=
  result = true ↔ (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)


def test1_a : Int := -5

def test1_b : Int := 10

def test1_Expected : Bool := true

def test3_a : Int := 5

def test3_b : Int := 10

def test3_Expected : Bool := false

def test5_a : Int := 0

def test5_b : Int := 10

def test5_Expected : Bool := false







section Proof
theorem test1_precondition :
  precondition test1_a test1_b := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  unfold postcondition test1_a test1_b test1_Expected
  simp only [eq_self_iff_true, true_iff]
  right
  constructor
  · decide
  · decide

theorem test3_precondition :
  precondition test3_a test3_b := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_a test3_b test3_Expected := by
  unfold postcondition test3_a test3_b test3_Expected
  simp only [Bool.false_eq_true]
  constructor
  · intro h
    exact h.elim
  · intro h
    cases h with
    | inl h1 => 
      have h2 : (10 : Int) < 0 := h1.2
      omega
    | inr h2 => 
      have h3 : (5 : Int) < 0 := h2.1
      omega

theorem test5_precondition :
  precondition test5_a test5_b := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition :
  postcondition test5_a test5_b test5_Expected := by
  unfold postcondition test5_a test5_b test5_Expected
  simp only [Bool.false_eq_true]
  constructor
  · intro h
    exact h.elim
  · intro h
    cases h with
    | inl h1 => omega
    | inr h2 => omega

theorem uniqueness (a : Int) (b : Int):
  precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  -- hpost1 : ret1 = true ↔ (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)
  -- hpost2 : ret2 = true ↔ (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)
  -- We need ret1 = ret2
  -- From Bool.eq_iff_iff: a = b ↔ (a ↔ b) for booleans
  rw [Bool.eq_iff_iff]
  -- Now we need: ret1 = true ↔ ret2 = true
  -- We have hpost1: ret1 = true ↔ P and hpost2: ret2 = true ↔ P
  -- So ret1 = true ↔ ret2 = true by transitivity through P
  exact Iff.trans hpost1 hpost2.symm
end Proof
