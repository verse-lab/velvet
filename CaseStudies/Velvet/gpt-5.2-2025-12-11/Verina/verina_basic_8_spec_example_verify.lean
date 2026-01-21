import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (a : Int) (b : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  result ≤ a ∧ result ≤ b ∧ (result = a ∨ result = b)


def test1_a : Int := 3

def test1_b : Int := 5

def test1_Expected : Int := 3

def test3_a : Int := 4

def test3_b : Int := 4

def test3_Expected : Int := 4

def test5_a : Int := 3

def test5_b : Int := -5

def test5_Expected : Int := -5







section Proof
theorem test1_precondition :
  precondition test1_a test1_b := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  unfold postcondition test1_a test1_b test1_Expected
  constructor
  · decide
  constructor
  · decide
  · left
    decide

theorem test3_precondition :
  precondition test3_a test3_b := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_a test3_b test3_Expected := by
  -- unfold definitions and reduce to a concrete arithmetic/equality goal
  simp [postcondition, test3_a, test3_b, test3_Expected]

theorem test5_precondition :
  precondition test5_a test5_b := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition :
  postcondition test5_a test5_b test5_Expected := by
  unfold postcondition
  simp [test5_a, test5_b, test5_Expected]

theorem uniqueness (a : Int) (b : Int) :
  precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  rcases h1 with ⟨h1_le_a, h1_le_b, h1_eq⟩
  rcases h2 with ⟨h2_le_a, h2_le_b, h2_eq⟩
  cases h1_eq with
  | inl hret1a =>
    cases h2_eq with
    | inl hret2a =>
      simpa [hret1a, hret2a]
    | inr hret2b =>
      have hab : a ≤ b := by simpa [hret1a] using h1_le_b
      have hba : b ≤ a := by simpa [hret2b] using h2_le_a
      have hab_eq : a = b := Int.le_antisymm hab hba
      calc
        ret1 = a := hret1a
        _ = b := hab_eq
        _ = ret2 := by simpa [hret2b]
  | inr hret1b =>
    cases h2_eq with
    | inl hret2a =>
      have hba : b ≤ a := by simpa [hret1b] using h1_le_a
      have hab : a ≤ b := by simpa [hret2a] using h2_le_b
      have hab_eq : a = b := Int.le_antisymm hab hba
      calc
        ret1 = b := hret1b
        _ = a := hab_eq.symm
        _ = ret2 := by simpa [hret2a]
    | inr hret2b =>
      simpa [hret1b, hret2b]
end Proof
