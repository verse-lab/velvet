import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (n : Int) :=
  True



def postcondition (n : Int) (result : Bool) :=
  result = true ↔ n % 11 = 0


def test1_n : Int := 0

def test1_Expected : Bool := true

def test2_n : Int := 11

def test2_Expected : Bool := true

def test6_n : Int := -11

def test6_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition test1_n test1_Expected
  simp [Int.zero_emod]

theorem test2_precondition :
  precondition test2_n := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_n test2_Expected := by
  unfold postcondition test2_n test2_Expected
  native_decide

theorem test6_precondition :
  precondition test6_n := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_n test6_Expected := by
  unfold postcondition test6_n test6_Expected
  native_decide

theorem uniqueness (n : Int):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  -- h1 : ret1 = true ↔ n % 11 = 0
  -- h2 : ret2 = true ↔ n % 11 = 0
  -- We need ret1 = ret2
  rw [Bool.eq_iff_iff]
  -- Now we need: (ret1 = true) ↔ (ret2 = true)
  -- This follows from h1 and h2 by transitivity
  exact h1.trans h2.symm
end Proof
