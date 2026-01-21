import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (a : Int) (b : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  result = a * b


def test1_a : Int := 3

def test1_b : Int := 4

def test1_Expected : Int := 12

def test4_a : Int := (-3)

def test4_b : Int := (-4)

def test4_Expected : Int := 12

def test5_a : Int := 0

def test5_b : Int := 5

def test5_Expected : Int := 0







section Proof
theorem test1_precondition :
  precondition test1_a test1_b := by
  intros; expose_names; exact (trivial); done


theorem test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test4

theorem test4_precondition :
  precondition test4_a test4_b := by
  intros; expose_names; exact (trivial); done


theorem test4_postcondition :
  postcondition test4_a test4_b test4_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test5

theorem test5_precondition :
  precondition test5_a test5_b := by
  intros; expose_names; exact (trivial); done


theorem test5_postcondition :
  postcondition test5_a test5_b test5_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (a : Int) (b : Int):
  precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  simp [postcondition] at h1 h2
  exact Eq.trans h1 (Eq.symm h2)
end Proof
