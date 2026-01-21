import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def HasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!



def precondition (a : Array Int) : Prop :=
  True



def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ HasConsecutivePair a)


def test1_a : Array Int := #[1, 2, 3, 5]

def test1_Expected : Bool := true

def test3_a : Array Int := #[]

def test3_Expected : Bool := false

def test7_a : Array Int := #[9, 9, 10]

def test7_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_a := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_Expected := by
  unfold postcondition
  -- goal: (test1_Expected = true ↔ HasConsecutivePair test1_a)
  simp [test1_Expected, test1_a, HasConsecutivePair]
  refine ⟨0, ?_, ?_⟩
  · decide
  · simp

theorem test3_precondition :
  precondition test3_a := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_a test3_Expected := by
  simp [postcondition, test3_a, test3_Expected, HasConsecutivePair, Nat.not_lt_zero]

theorem test7_precondition :
  precondition test7_a := by
  intros; expose_names; exact (trivial); done

theorem test7_postcondition :
  postcondition test7_a test7_Expected := by
  unfold postcondition
  simp [test7_a, test7_Expected, HasConsecutivePair]
  refine ⟨1, ?_, ?_⟩
  · decide
  · decide

theorem uniqueness (a : Array Int) :
  precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  -- hpost1 : (ret1 = true ↔ HasConsecutivePair a)
  -- hpost2 : (ret2 = true ↔ HasConsecutivePair a)
  have hiff : (ret1 = true ↔ ret2 = true) := by
    exact Iff.trans hpost1 (Iff.symm hpost2)
  cases ret1 <;> cases ret2 <;> simp at hiff <;> simp
end Proof
