import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def allDigitsBool (s : String) : Bool :=
  s.toList.all Char.isDigit



def precondition (s : String) : Prop :=
  True




def postcondition (s : String) (result : Bool) : Prop :=
  result = allDigitsBool s


def test1_s : String := "123456"

def test1_Expected : Bool := true

def test2_s : String := "123a56"

def test2_Expected : Bool := false

def test3_s : String := ""

def test3_Expected : Bool := true







section Proof
theorem test1_precondition : precondition test1_s := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_s test1_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test2_precondition : precondition test2_s := by
    intros; expose_names; exact (trivial); done

theorem test2_postcondition : postcondition test2_s test2_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test3_precondition : precondition test3_s := by
    intros; expose_names; exact (trivial); done

theorem test3_postcondition : postcondition test3_s test3_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness
    (s : String)
    : precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hs
  intro ret1 ret2 h1 h2
  -- Unfold postcondition: ret = allDigitsBool s, then both are equal to same value
  simpa [postcondition] using h1.trans h2.symm
end Proof
