import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def gaussSumCal (N : Nat) : Nat :=
  N * (N + 1) / 2

def precondition (N : Nat) : Prop :=
  True

def postcondition (N : Nat) (result : Nat) : Prop :=
  result = gaussSumCal N


def test1_N : Nat := 0

def test1_Expected : Nat := 0

def test3_N : Nat := 5

def test3_Expected : Nat := 15

def test4_N : Nat := 10

def test4_Expected : Nat := 55







section Proof
theorem test1_precondition : precondition test1_N := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_N test1_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test3_precondition : precondition test3_N := by
    intros; expose_names; exact (trivial); done

theorem test3_postcondition : postcondition test3_N test3_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test4_precondition : precondition test4_N := by
    intros; expose_names; exact (trivial); done

theorem test4_postcondition : postcondition test4_N test4_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness
    (N : Nat)
    : precondition N →
  (∀ ret1 ret2,
    postcondition N ret1 →
    postcondition N ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  simp [postcondition] at h1 h2
  exact Eq.trans h1 (Eq.symm h2)
end Proof
