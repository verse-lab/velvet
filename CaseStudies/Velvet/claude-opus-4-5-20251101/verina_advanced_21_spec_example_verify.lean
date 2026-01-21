import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000






def isPalindromeProperty (s : String) : Prop :=
  s.toList = s.toList.reverse



def ensures1 (s : String) (result : Bool) :=
  result = true ↔ isPalindromeProperty s

def precondition (s : String) :=
  True

def postcondition (s : String) (result : Bool) :=
  ensures1 s result


def test1_s : String := "racecar"

def test1_Expected : Bool := true

def test3_s : String := "abc"

def test3_Expected : Bool := false

def test4_s : String := ""

def test4_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition ensures1 isPalindromeProperty test1_s test1_Expected
  native_decide

theorem test3_precondition :
  precondition test3_s := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
  unfold postcondition ensures1 isPalindromeProperty test3_s test3_Expected
  native_decide

theorem test4_precondition :
  precondition test4_s := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_s test4_Expected := by
  unfold postcondition ensures1 isPalindromeProperty test4_s test4_Expected
  simp [String.toList]

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- hpost1 : ret1 = true ↔ isPalindromeProperty s
  -- hpost2 : ret2 = true ↔ isPalindromeProperty s
  unfold postcondition ensures1 at hpost1 hpost2
  -- We need to show ret1 = ret2
  -- Using Bool.eq_iff_iff: a = b ↔ (a = true ↔ b = true)
  rw [Bool.eq_iff_iff]
  -- Now we need: ret1 = true ↔ ret2 = true
  -- We have: ret1 = true ↔ isPalindromeProperty s (from hpost1)
  -- We have: ret2 = true ↔ isPalindromeProperty s (from hpost2)
  -- So: ret1 = true ↔ ret2 = true by transitivity with symmetry
  exact Iff.trans hpost1 hpost2.symm
end Proof
