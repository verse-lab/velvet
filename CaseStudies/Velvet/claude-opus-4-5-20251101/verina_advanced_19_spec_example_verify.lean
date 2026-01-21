import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def cleanString (s : String) : List Char :=
  (s.toList.filter Char.isAlpha).map Char.toLower


def isPalindrome (chars : List Char) : Prop :=
  chars = chars.reverse



def ensures1 (s : String) (result : Bool) :=
  result = true ↔ cleanString s = (cleanString s).reverse

def precondition (s : String) :=
  True

def postcondition (s : String) (result : Bool) :=
  ensures1 s result


def test1_s : String := "A man, a plan, a canal, Panama"

def test1_Expected : Bool := true

def test3_s : String := "OpenAI"

def test3_Expected : Bool := false

def test6_s : String := ""

def test6_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition ensures1 test1_s test1_Expected cleanString
  native_decide

theorem test3_precondition :
  precondition test3_s := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
  unfold postcondition ensures1 test3_s test3_Expected cleanString
  native_decide

theorem test6_precondition :
  precondition test6_s := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_s test6_Expected := by
  unfold postcondition ensures1 test6_s test6_Expected cleanString
  native_decide

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _
  intro ret1 ret2 h1 h2
  unfold postcondition ensures1 at h1 h2
  -- h1 : ret1 = true ↔ cleanString s = (cleanString s).reverse
  -- h2 : ret2 = true ↔ cleanString s = (cleanString s).reverse
  rw [Bool.eq_iff_iff]
  -- Goal: ret1 = true ↔ ret2 = true
  constructor
  · intro hret1
    rw [hret1] at h1
    -- h1 : true = true ↔ cleanString s = (cleanString s).reverse
    have hP : cleanString s = (cleanString s).reverse := h1.mp rfl
    exact h2.mpr hP
  · intro hret2
    rw [hret2] at h2
    have hP : cleanString s = (cleanString s).reverse := h2.mp rfl
    exact h1.mpr hP
end Proof
