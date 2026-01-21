import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000







def isSortedProp (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < a.size → j < a.size → i < j → a[i]! ≤ a[j]!



def precondition (a : Array Int) : Prop :=
  True



def postcondition (a : Array Int) (result : Bool) : Prop :=
  result = true ↔ isSortedProp a


def test1_a : Array Int := #[1, 2, 3, 4, 5]

def test1_Expected : Bool := true

def test4_a : Array Int := #[]

def test4_Expected : Bool := true

def test6_a : Array Int := #[2, 2, 2, 2]

def test6_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_a := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_Expected := by
  unfold postcondition test1_a test1_Expected
  constructor
  · -- Forward: true = true → isSortedProp #[1, 2, 3, 4, 5]
    intro _
    unfold isSortedProp
    intro i j hi hj hij
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hi hj
    -- hi : i < 5, hj : j < 5, hij : i < j
    -- Need to show #[1, 2, 3, 4, 5][i]! ≤ #[1, 2, 3, 4, 5][j]!
    interval_cases i <;> interval_cases j <;> simp_all <;> native_decide
  · -- Backward: isSortedProp #[1, 2, 3, 4, 5] → true = true
    intro _
    rfl

theorem test4_precondition :
  precondition test4_a := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_a test4_Expected := by
  unfold postcondition test4_a test4_Expected isSortedProp
  constructor
  · intro _
    intros i j hi hj _
    simp only [Array.size_empty] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro _
    rfl

theorem test6_precondition :
  precondition test6_a := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_a test6_Expected := by
  unfold postcondition test6_a test6_Expected isSortedProp
  constructor
  · intro _
    intro i j hi hj hij
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;> simp_all
  · intro _
    rfl

theorem uniqueness (a : Array Int):
  precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- hpost1 : ret1 = true ↔ isSortedProp a
  -- hpost2 : ret2 = true ↔ isSortedProp a
  -- We need to show ret1 = ret2
  -- Using Bool.eq_iff_iff: a = b ↔ (a = true ↔ b = true)
  rw [Bool.eq_iff_iff]
  -- Now goal is: ret1 = true ↔ ret2 = true
  -- hpost1: ret1 = true ↔ isSortedProp a
  -- hpost2: ret2 = true ↔ isSortedProp a
  -- So ret1 = true ↔ isSortedProp a ↔ ret2 = true
  unfold postcondition at hpost1 hpost2
  exact Iff.trans hpost1 hpost2.symm
end Proof
