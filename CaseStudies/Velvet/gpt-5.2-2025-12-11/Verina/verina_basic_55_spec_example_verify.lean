import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (a : Int) (b : Int) : Prop :=
  True




def postcondition (a : Int) (b : Int) (result : Bool) : Prop :=
  (result = true ↔ a = b) ∧ (result = false ↔ a ≠ b)


def test1_a : Int := 1

def test1_b : Int := 1

def test1_Expected : Bool := true

def test2_a : Int := 1

def test2_b : Int := 2

def test2_Expected : Bool := false

def test3_a : Int := (-5)

def test3_b : Int := (-5)

def test3_Expected : Bool := true







section Proof
theorem test1_precondition : precondition test1_a test1_b := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_a test1_b test1_Expected := by
  unfold postcondition
  simp [test1_a, test1_b, test1_Expected]

theorem test2_precondition : precondition test2_a test2_b := by
    intros; expose_names; exact (trivial); done

theorem test2_postcondition : postcondition test2_a test2_b test2_Expected := by
  unfold postcondition
  simp [test2_a, test2_b, test2_Expected]

theorem test3_precondition : precondition test3_a test3_b := by
    intros; expose_names; exact (trivial); done

theorem test3_postcondition : postcondition test3_a test3_b test3_Expected := by
  unfold postcondition test3_a test3_b test3_Expected
  simp

theorem uniqueness
    (a : Int)
    (b : Int)
    : precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  rcases hpost1 with ⟨h1t, h1f⟩
  rcases hpost2 with ⟨h2t, h2f⟩
  cases ret1 <;> cases ret2 <;> try rfl
  · -- ret1 = false, ret2 = true
    have hab : a = b := by
      exact (h2t).1 rfl
    have hne : a ≠ b := by
      exact (h1f).1 rfl
    exact False.elim (hne hab)
  · -- ret1 = true, ret2 = false
    have hab : a = b := by
      exact (h1t).1 rfl
    have hne : a ≠ b := by
      exact (h2f).1 rfl
    exact False.elim (hne hab)
end Proof
