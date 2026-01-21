import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (n : Nat) :=
  True






def postcondition (n : Nat) (result : Nat) :=
  result = (Nat.digits 10 n).sum


def test1_n : Nat := 12345

def test1_Expected : Nat := 15

def test2_n : Nat := 0

def test2_Expected : Nat := 0

def test5_n : Nat := 1001

def test5_Expected : Nat := 2







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done


theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test2

theorem test2_precondition :
  precondition test2_n := by
  intros; expose_names; exact (trivial); done


theorem test2_postcondition :
  postcondition test2_n test2_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test5

theorem test5_precondition :
  precondition test5_n := by
  intros; expose_names; exact (trivial); done


theorem test5_postcondition :
  postcondition test5_n test5_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (n : Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  rw [hpost1, hpost2]
end Proof
