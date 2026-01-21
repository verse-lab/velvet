import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def hasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!



def ensures1 (a : Array Int) (result : Bool) :=
  result = true ↔ hasConsecutivePair a

def precondition (a : Array Int) :=
  True

def postcondition (a : Array Int) (result : Bool) :=
  ensures1 a result


def test1_a : Array Int := #[1, 2, 3, 5]

def test1_Expected : Bool := true

def test3_a : Array Int := #[]

def test3_Expected : Bool := false

def test5_a : Array Int := #[5, 6]

def test5_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_a := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_Expected := by
  unfold postcondition ensures1 test1_a test1_Expected hasConsecutivePair
  constructor
  · intro _
    refine ⟨0, ?_, ?_⟩
    · native_decide
    · native_decide
  · intro _
    rfl

theorem test3_precondition :
  precondition test3_a := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_a test3_Expected := by
  unfold postcondition ensures1 test3_a test3_Expected hasConsecutivePair
  constructor
  · intro h
    simp [Bool.false_eq_true] at h
  · intro ⟨i, hi, _⟩
    simp [Array.size_empty] at hi

theorem test5_precondition :
  precondition test5_a := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition :
  postcondition test5_a test5_Expected := by
  unfold postcondition ensures1 test5_a test5_Expected hasConsecutivePair
  constructor
  · intro _
    use 0
    native_decide
  · intro _
    rfl

theorem uniqueness (a : Array Int):
  precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  unfold postcondition ensures1 at hpost1 hpost2
  rw [Bool.eq_iff_iff]
  constructor
  · intro h1
    exact hpost2.mpr (hpost1.mp h1)
  · intro h2
    exact hpost1.mpr (hpost2.mp h2)
end Proof
