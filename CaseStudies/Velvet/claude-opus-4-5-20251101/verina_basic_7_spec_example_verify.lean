import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000










def precondition (n : Nat) :=
  True

def postcondition (n : Nat) (result : Nat) :=
  result = (n * (2 * n - 1) * (2 * n + 1)) / 3


def test1_n : Nat := 0

def test1_Expected : Nat := 0

def test2_n : Nat := 1

def test2_Expected : Nat := 1

def test3_n : Nat := 2

def test3_Expected : Nat := 10







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

-- test3

theorem test3_precondition :
  precondition test3_n := by
  intros; expose_names; exact (trivial); done


theorem test3_postcondition :
  postcondition test3_n test3_Expected := by
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
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  rw [h1, h2]
end Proof
