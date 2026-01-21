import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (a : Int) (b : Int) :=
  True



def postcondition (a : Int) (b : Int) (result : Int) :=
  result = a * b


def test1_a : Int := 3

def test1_b : Int := 4

def test1_Expected : Int := 12

def test2_a : Int := 3

def test2_b : Int := -4

def test2_Expected : Int := -12

def test4_a : Int := -3

def test4_b : Int := -4

def test4_Expected : Int := 12







section Proof
theorem test1_precondition :
  precondition test1_a test1_b := by
  intros; expose_names; exact (trivial); done


theorem test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test2

theorem test2_precondition :
  precondition test2_a test2_b := by
  intros; expose_names; exact (trivial); done


theorem test2_postcondition :
  postcondition test2_a test2_b test2_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test4

theorem test4_precondition :
  precondition test4_a test4_b := by
  intros; expose_names; exact (trivial); done


theorem test4_postcondition :
  postcondition test4_a test4_b test4_Expected := by
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
  intro _
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  rw [h1, h2]
end Proof
