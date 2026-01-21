import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isDigitChar (c : Char) : Bool :=
  c.isDigit


def digitCount (s : String) : Nat :=
  (s.toList.countP (fun c => isDigitChar c))



def precondition (s : String) : Prop :=
  True




def postcondition (s : String) (result : Nat) : Prop :=
  result = digitCount s


def test1_s : String := "123abc456"

def test1_Expected : Nat := 6

def test3_s : String := "1234567890"

def test3_Expected : Nat := 10

def test8_s : String := " 9!x-0?"

def test8_Expected : Nat := 2







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done


theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test3

theorem test3_precondition :
  precondition test3_s := by
  intros; expose_names; exact (trivial); done


theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test8

theorem test8_precondition :
  precondition test8_s := by
  intros; expose_names; exact (trivial); done


theorem test8_postcondition :
  postcondition test8_s test8_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  simp [postcondition] at h1 h2
  rw [h1, h2]
end Proof
