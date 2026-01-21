import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def OddIndexElementsOdd (a : Array Int) : Prop :=
  ∀ (i : Nat), i < a.size → i % 2 = 1 → (a[i]!) % 2 ≠ 0



def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Bool) : Prop :=
  result = true ↔ OddIndexElementsOdd a


def test1_a : Array Int := #[1, 2, 3, 4, 5]

def test1_Expected : Bool := false

def test2_a : Array Int := #[1, 3, 5, 7, 9]

def test2_Expected : Bool := true

def test4_a : Array Int := #[]

def test4_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_a := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_Expected := by
  unfold postcondition
  -- Reduce constants; `simp` turns `false = true` into `False` and the array/indexing/mod facts.
  simp [test1_a, test1_Expected, OddIndexElementsOdd]
  -- Goal is now an existential counterexample; choose index 1.
  refine ⟨1, by decide, by decide, ?_⟩
  -- At index 1 the value is 2, which is divisible by 2.
  decide

theorem test2_precondition :
  precondition test2_a := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_a test2_Expected := by
  -- unfold the postcondition and concrete constants
  simp [postcondition, test2_a, test2_Expected, OddIndexElementsOdd]
  intro i hi hmod
  -- for i < 5, check each possible index; only odd indices matter
  have hi' : i < 5 := hi
  revert hmod
  -- enumerate i = 0,1,2,3,4 using interval_cases
  interval_cases i <;> intro hmod
  · -- i = 0
    simp at hmod
  · -- i = 1, a[1]! = 3
    simp
  · -- i = 2
    simp at hmod
  · -- i = 3, a[3]! = 7
    simp
  · -- i = 4
    simp at hmod

theorem test4_precondition :
  precondition test4_a := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_a test4_Expected := by
  -- unfold the postcondition and concrete test data
  simp [postcondition, test4_a, test4_Expected, OddIndexElementsOdd, Array.size_empty, Nat.not_lt_zero]

theorem uniqueness (a : Array Int):
  precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- unfold postcondition and compare truth values
  unfold postcondition at hpost1 hpost2
  -- derive (ret1 = true ↔ ret2 = true)
  have hiff : (ret1 = true ↔ ret2 = true) :=
    Iff.trans hpost1 (Iff.symm hpost2)
  -- conclude by case analysis on ret1
  cases ret1 <;> cases ret2 <;> simp at hiff <;> try rfl
end Proof
