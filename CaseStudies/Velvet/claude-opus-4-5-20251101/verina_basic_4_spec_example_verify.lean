import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (arr : Array Int) (k : Nat) : Prop :=
  arr.size > 0 ∧ k ≥ 1 ∧ k ≤ arr.size



def postcondition (arr : Array Int) (k : Nat) (result : Int) : Prop :=
  result = arr[k - 1]!


def test1_arr : Array Int := #[10, 20, 30, 40, 50]

def test1_k : Nat := 1

def test1_Expected : Int := 10

def test2_arr : Array Int := #[10, 20, 30, 40, 50]

def test2_k : Nat := 3

def test2_Expected : Int := 30

def test4_arr : Array Int := #[5]

def test4_k : Nat := 1

def test4_Expected : Int := 5







section Proof
theorem test1_precondition :
  precondition test1_arr test1_k := by
  unfold precondition test1_arr test1_k
  native_decide


theorem test1_postcondition :
  postcondition test1_arr test1_k test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test2

theorem test2_precondition :
  precondition test2_arr test2_k := by
  unfold precondition test2_arr test2_k
  native_decide


theorem test2_postcondition :
  postcondition test2_arr test2_k test2_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test4

theorem test4_precondition :
  precondition test4_arr test4_k := by
  unfold precondition test4_arr test4_k
  native_decide


theorem test4_postcondition :
  postcondition test4_arr test4_k test4_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (arr : Array Int) (k : Nat):
  precondition arr k →
  (∀ ret1 ret2,
    postcondition arr k ret1 →
    postcondition arr k ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  rw [hpost1, hpost2]
end Proof
