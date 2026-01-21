import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def oddSquaresClosedFormNumerator (n : Nat) : Nat :=
  n * (2 * n - 1) * (2 * n + 1)



def precondition (n : Nat) : Prop :=
  True






def postcondition (n : Nat) (result : Nat) : Prop :=
  result = oddSquaresClosedFormNumerator n / 3


def test1_n : Nat := 0

def test1_Expected : Nat := 0

def test3_n : Nat := 2

def test3_Expected : Nat := 10

def test7_n : Nat := 10

def test7_Expected : Nat := 1330







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done


theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test3

theorem test3_precondition :
  precondition test3_n := by
  intros; expose_names; exact (trivial); done


theorem test3_postcondition :
  postcondition test3_n test3_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test7

theorem test7_precondition :
  precondition test7_n := by
  intros; expose_names; exact (trivial); done


theorem test7_postcondition :
  postcondition test7_n test7_Expected := by
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
  intro _hn
  intro ret1 ret2 h1 h2
  simp [postcondition] at h1 h2
  -- h1 : ret1 = oddSquaresClosedFormNumerator n / 3
  -- h2 : ret2 = oddSquaresClosedFormNumerator n / 3
  rw [h1, h2]
end Proof
