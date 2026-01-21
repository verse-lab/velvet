import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (n : Int) (a : Array Int) :=
  a.size > 0



def postcondition (n : Int) (a : Array Int) (result : Bool) :=
  result = true ↔ ∀ i : Nat, i < a.size → a[i]! < n


def test1_n : Int := 6

def test1_a : Array Int := #[1, 2, 3, 4, 5]

def test1_Expected : Bool := true

def test2_n : Int := 3

def test2_a : Array Int := #[1, 2, 3, 4, 5]

def test2_Expected : Bool := false

def test4_n : Int := -1

def test4_a : Array Int := #[-10, -5, -3]

def test4_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_n test1_a := by
  unfold precondition test1_a
  decide

theorem test1_postcondition :
  postcondition test1_n test1_a test1_Expected := by
  unfold postcondition test1_n test1_a test1_Expected
  constructor
  · intro _
    intro i hi
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hi
    interval_cases i <;> native_decide
  · intro _
    rfl

theorem test2_precondition :
  precondition test2_n test2_a := by
  unfold precondition test2_a
  decide

theorem test2_postcondition :
  postcondition test2_n test2_a test2_Expected := by
  unfold postcondition test2_n test2_a test2_Expected
  simp only [Bool.false_eq_true, false_iff]
  intro h
  have : #[1, 2, 3, 4, 5][2]! < (3 : Int) := h 2 (by decide)
  simp at this

theorem test4_precondition :
  precondition test4_n test4_a := by
  unfold precondition test4_a
  decide

theorem test4_postcondition :
  postcondition test4_n test4_a test4_Expected := by
  unfold postcondition test4_n test4_a test4_Expected
  constructor
  · intro _
    intro i hi
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hi
    interval_cases i <;> native_decide
  · intro _
    rfl

theorem uniqueness (n : Int) (a : Array Int):
  precondition n a →
  (∀ ret1 ret2,
    postcondition n a ret1 →
    postcondition n a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  rw [Bool.eq_iff_iff]
  constructor
  · intro h1
    rw [h1] at hpost1
    have hP : ∀ i : Nat, i < a.size → a[i]! < n := hpost1.mp rfl
    exact hpost2.mpr hP
  · intro h2
    rw [h2] at hpost2
    have hP : ∀ i : Nat, i < a.size → a[i]! < n := hpost2.mp rfl
    exact hpost1.mpr hP
end Proof
