import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def normalizedChars (s : String) : List Char :=
  (s.toList.filter Char.isAlphanum).map Char.toLower


def postcondition_clause (s : String) (result : Bool) :=
  let normalized := normalizedChars s
  result = (normalized == normalized.reverse)

def precondition (s : String) :=
  True

def postcondition (s : String) (result : Bool) :=
  postcondition_clause s result


def test1_s : String := "A man, a plan, a canal: Panama"

def test1_Expected : Bool := true

def test3_s : String := "race a car"

def test3_Expected : Bool := false

def test4_s : String := "No 'x' in Nixon"

def test4_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done


theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test3

theorem test3_precondition :
  precondition test3_s := by
  intros; expose_names; exact (trivial); done


theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test4

theorem test4_precondition :
  precondition test4_s := by
  intros; expose_names; exact (trivial); done


theorem test4_postcondition :
  postcondition test4_s test4_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _
  intro ret1 ret2 h1 h2
  unfold postcondition postcondition_clause at h1 h2
  simp only at h1 h2
  rw [h1, h2]
end Proof
