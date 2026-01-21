import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def hasDigit8 (n : Nat) : Prop :=
  ∃ k : Nat, (n / (10^k)) % 10 = 8



def ensures1 (n : Int) (result : Bool) :=
  result = true ↔ (n % 8 = 0 ∨ hasDigit8 (Int.natAbs n))

def precondition (n : Int) :=
  True

def postcondition (n : Int) (result : Bool) :=
  ensures1 n result


def test1_n : Int := 8

def test1_Expected : Bool := true

def test3_n : Int := 1224

def test3_Expected : Bool := true

def test4_n : Int := 73

def test4_Expected : Bool := false







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition ensures1 test1_n test1_Expected
  constructor
  · intro _
    left
    native_decide
  · intro _
    rfl

theorem test3_precondition :
  precondition test3_n := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_n test3_Expected := by
  unfold postcondition ensures1 test3_n test3_Expected
  constructor
  · intro _
    left
    native_decide
  · intro _
    rfl

theorem test4_precondition :
  precondition test4_n := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_n test4_Expected := by
  unfold postcondition ensures1 test4_n test4_Expected hasDigit8
  constructor
  · intro h
    cases h
  · intro h
    cases h with
    | inl h1 => 
      have : (73 : Int) % 8 = 1 := by native_decide
      omega
    | inr h2 =>
      obtain ⟨k, hk⟩ := h2
      have h1 : k = 0 ∨ k = 1 ∨ k ≥ 2 := by omega
      rcases h1 with rfl | rfl | hk2
      · norm_num at hk
      · norm_num at hk
      · have hpow : 10 ^ k ≥ 100 := by
          calc 10 ^ k ≥ 10 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
               _ = 100 := by norm_num
        have h73_lt : 73 < 10 ^ k := by omega
        have hdiv : 73 / 10 ^ k = 0 := Nat.div_eq_zero_iff.mpr (Or.inr h73_lt)
        simp [hdiv] at hk

theorem uniqueness (n : Int):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _pre ret1 ret2 h1 h2
  -- h1 : ret1 = true ↔ (n % 8 = 0 ∨ hasDigit8 (Int.natAbs n))
  -- h2 : ret2 = true ↔ (n % 8 = 0 ∨ hasDigit8 (Int.natAbs n))
  unfold postcondition ensures1 at h1 h2
  -- Now h1 and h2 are both biconditionals with the same RHS
  -- We need to show ret1 = ret2
  rw [Bool.eq_iff_iff]
  -- Now we need: ret1 = true ↔ ret2 = true
  constructor
  · intro hr1
    exact h2.mpr (h1.mp hr1)
  · intro hr2
    exact h1.mpr (h2.mp hr2)
end Proof
