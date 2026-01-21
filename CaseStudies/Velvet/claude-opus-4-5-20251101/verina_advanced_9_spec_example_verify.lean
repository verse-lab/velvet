import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def digitSum (n : Nat) : Nat :=
  if n < 10 then n
  else (n % 10) + digitSum (n / 10)



def precondition (n : Nat) (d : Nat) : Prop :=
  d > 0





def postcondition (n : Nat) (d : Nat) (result : Nat) : Prop :=
  result = (Finset.filter (fun k => d ∣ digitSum k) (Finset.range n)).card


def test1_n : Nat := 0

def test1_d : Nat := 2

def test1_Expected : Nat := 0

def test2_n : Nat := 1

def test2_d : Nat := 2

def test2_Expected : Nat := 1

def test6_n : Nat := 5

def test6_d : Nat := 1

def test6_Expected : Nat := 5







section Proof
theorem test1_precondition :
  precondition test1_n test1_d := by
  unfold precondition test1_d
  decide


theorem test1_postcondition :
  postcondition test1_n test1_d test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test2

theorem test2_precondition :
  precondition test2_n test2_d := by
  unfold precondition test2_d
  decide

theorem test2_postcondition :
  postcondition test2_n test2_d test2_Expected := by
  unfold postcondition test2_n test2_d test2_Expected
  native_decide

theorem test6_precondition :
  precondition test6_n test6_d := by
  unfold precondition test6_d
  decide

theorem test6_postcondition :
  postcondition test6_n test6_d test6_Expected := by
  unfold postcondition test6_n test6_d test6_Expected
  native_decide

theorem uniqueness (n : Nat) (d : Nat):
  precondition n d →
  (∀ ret1 ret2,
    postcondition n d ret1 →
    postcondition n d ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  rw [hpost1, hpost2]
end Proof
