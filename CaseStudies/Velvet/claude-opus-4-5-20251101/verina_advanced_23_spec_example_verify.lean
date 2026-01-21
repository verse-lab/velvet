import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def isPowerOfTwoProp (n : Int) : Prop :=
  n > 0 ∧ ∃ x : Nat, n = (2 : Int) ^ x

def ensures1 (n : Int) (result : Bool) :=
  result = true ↔ isPowerOfTwoProp n

def precondition (n : Int) :=
  True

def postcondition (n : Int) (result : Bool) :=
  ensures1 n result


def test1_n : Int := 1

def test1_Expected : Bool := true

def test2_n : Int := 16

def test2_Expected : Bool := true

def test4_n : Int := 0

def test4_Expected : Bool := false







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition ensures1 isPowerOfTwoProp test1_n test1_Expected
  constructor
  · intro _
    constructor
    · omega
    · use 0
      native_decide
  · intro _
    rfl

theorem test2_precondition :
  precondition test2_n := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_n test2_Expected := by
  unfold postcondition ensures1 isPowerOfTwoProp test2_n test2_Expected
  constructor
  · intro _
    constructor
    · omega
    · use 4
      native_decide
  · intro _
    rfl

theorem test4_precondition :
  precondition test4_n := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_n test4_Expected := by
  unfold postcondition ensures1 isPowerOfTwoProp test4_n test4_Expected
  apply iff_of_false
  · exact Bool.false_ne_true
  · intro ⟨h, _⟩
    omega

theorem uniqueness (n : Int):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- hpost1 : ret1 = true ↔ isPowerOfTwoProp n
  -- hpost2 : ret2 = true ↔ isPowerOfTwoProp n
  -- We need to show ret1 = ret2
  unfold postcondition ensures1 at hpost1 hpost2
  -- Using Bool.eq_iff_iff: a = b ↔ (a = true ↔ b = true)
  rw [Bool.eq_iff_iff]
  -- Now we need: ret1 = true ↔ ret2 = true
  -- We have: ret1 = true ↔ isPowerOfTwoProp n (from hpost1)
  -- We have: ret2 = true ↔ isPowerOfTwoProp n (from hpost2)
  -- So ret1 = true ↔ ret2 = true by transitivity with symmetry
  exact hpost1.trans hpost2.symm
end Proof
