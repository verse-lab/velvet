import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (size : Nat) : Prop :=
  True

def postcondition (size : Nat) (result : Nat) : Prop :=
  result = 6 * (size ^ 2)


def test1_size : Nat := 3

def test1_Expected : Nat := 54

def test2_size : Nat := 1

def test2_Expected : Nat := 6

def test6_size : Nat := 0

def test6_Expected : Nat := 0







section Proof
theorem test1_precondition :
  precondition test1_size := by
  intros; expose_names; exact (trivial); done


theorem test1_postcondition :
  postcondition test1_size test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test2

theorem test2_precondition :
  precondition test2_size := by
  intros; expose_names; exact (trivial); done


theorem test2_postcondition :
  postcondition test2_size test2_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test6

theorem test6_precondition :
  precondition test6_size := by
  intros; expose_names; exact (trivial); done


theorem test6_postcondition :
  postcondition test6_size test6_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (size : Nat):
  precondition size →
  (∀ ret1 ret2,
    postcondition size ret1 →
    postcondition size ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  simp [postcondition] at hpost1 hpost2
  exact hpost1.trans hpost2.symm
end Proof
