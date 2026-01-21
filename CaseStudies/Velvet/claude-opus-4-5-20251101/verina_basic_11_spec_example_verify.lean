import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (n : Nat) :=
  True



def ensures1 (n : Nat) (result : Nat) :=
  result = n % 10


def ensures2 (n : Nat) (result : Nat) :=
  result < 10

def postcondition (n : Nat) (result : Nat) :=
  ensures1 n result ∧
  ensures2 n result


def test1_n : Nat := 123

def test1_Expected : Nat := 3

def test2_n : Nat := 0

def test2_Expected : Nat := 0

def test8_n : Nat := 5

def test8_Expected : Nat := 5







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition ensures1 ensures2 test1_n test1_Expected
  constructor
  · native_decide
  · native_decide

theorem test2_precondition :
  precondition test2_n := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_n test2_Expected := by
  unfold postcondition ensures1 ensures2 test2_n test2_Expected
  constructor
  · native_decide
  · native_decide

theorem test8_precondition :
  precondition test8_n := by
  intros; expose_names; exact (trivial); done

theorem test8_postcondition :
  postcondition test8_n test8_Expected := by
  unfold postcondition ensures1 ensures2 test8_n test8_Expected
  native_decide

theorem uniqueness (n : Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  unfold ensures1 at hpost1 hpost2
  have h1 : ret1 = n % 10 := hpost1.left
  have h2 : ret2 = n % 10 := hpost2.left
  rw [h1, h2]
end Proof
