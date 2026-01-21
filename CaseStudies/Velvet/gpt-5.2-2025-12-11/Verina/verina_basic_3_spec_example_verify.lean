import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000






def precondition (n : Int) :=
  True

def postcondition (n : Int) (result : Bool) :=
  result = true ↔ (11 : Int) ∣ n


def test1_n : Int := 0

def test1_Expected : Bool := true

def test2_n : Int := 11

def test2_Expected : Bool := true

def test4_n : Int := 23

def test4_Expected : Bool := false







section Proof

theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition test1_n test1_Expected
  constructor
  · intro _
    exact Int.dvd_zero 11
  · intro _
    rfl


theorem test2_precondition :
  precondition test2_n := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem test2_postcondition :
  postcondition test2_n test2_Expected := by
  unfold postcondition test2_n test2_Expected
  constructor
  · intro _
    exact dvd_refl 11
  · intro _
    rfl


theorem test4_precondition :
  precondition test4_n := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem test4_postcondition :
  postcondition test4_n test4_Expected := by
  unfold postcondition test4_n test4_Expected
  constructor
  · intro h
    exact False.elim (Bool.false_ne_true h)
  · intro h
    have : (23 : Int) % 11 = 1 := by decide
    have : ¬((11 : Int) ∣ 23) := by
      rw [Int.dvd_iff_emod_eq_zero]
      omega
    contradiction


theorem uniqueness (n : Int):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _ ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  rw [Bool.eq_iff_iff]
  exact Iff.trans h1 h2.symm

end Proof
