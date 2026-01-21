import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isPowerOfFour (n : Nat) : Prop :=
  ∃ x : Nat, 4 ^ x = n



def ensures1 (n : Nat) (result : Bool) :=
  result = true ↔ isPowerOfFour n

def precondition (n : Nat) :=
  True

def postcondition (n : Nat) (result : Bool) :=
  ensures1 n result


def test2_n : Nat := 1

def test2_Expected : Bool := true

def test4_n : Nat := 4

def test4_Expected : Bool := true

def test6_n : Nat := 16

def test6_Expected : Bool := true

def test1_n : Nat := 0

def test1_Expected : Bool := false







section Proof
theorem test2_precondition :
  precondition test2_n := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_n test2_Expected := by
  unfold postcondition ensures1 test2_n test2_Expected isPowerOfFour
  constructor
  · intro _
    exact ⟨0, rfl⟩
  · intro _
    rfl

theorem test4_precondition :
  precondition test4_n := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_n test4_Expected := by
  unfold postcondition ensures1 test4_n test4_Expected isPowerOfFour
  constructor
  · intro _
    exact ⟨1, rfl⟩
  · intro _
    rfl

theorem test6_precondition :
  precondition test6_n := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_n test6_Expected := by
  unfold postcondition ensures1 test6_n test6_Expected isPowerOfFour
  constructor
  · intro _
    exact ⟨2, rfl⟩
  · intro _
    rfl

theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition ensures1 test1_n test1_Expected isPowerOfFour
  constructor
  · intro h
    exact False.elim (by cases h)
  · intro ⟨x, hx⟩
    have h4pos : 0 < 4 := by decide
    have hpow_pos : 0 < 4 ^ x := Nat.pow_pos h4pos
    omega

theorem uniqueness (n : Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition ensures1 at hpost1 hpost2
  -- hpost1 : ret1 = true ↔ isPowerOfFour n
  -- hpost2 : ret2 = true ↔ isPowerOfFour n
  rw [Bool.eq_iff_iff]
  -- Goal: ret1 = true ↔ ret2 = true
  exact Iff.trans hpost1 hpost2.symm
end Proof
