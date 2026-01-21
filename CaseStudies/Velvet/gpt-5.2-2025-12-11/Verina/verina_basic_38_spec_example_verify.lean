import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def allEq (l : List Char) (c : Char) : Bool :=
  l.all (fun d => d = c)

def allCharactersSameSpec (s : String) : Bool :=
  match s.toList with
  | [] => true
  | c :: cs => allEq cs c

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Bool) : Prop :=
  result = true ↔ allCharactersSameSpec s = true


def test1_s : String := "aaa"

def test1_Expected : Bool := true

def test2_s : String := "aba"

def test2_Expected : Bool := false

def test3_s : String := ""

def test3_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done


theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test2

theorem test2_precondition :
  precondition test2_s := by
  intros; expose_names; exact (trivial); done


theorem test2_postcondition :
  postcondition test2_s test2_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test3

theorem test3_precondition :
  precondition test3_s := by
  intros; expose_names; exact (trivial); done


theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
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
  unfold postcondition at h1 h2
  have h : (ret1 = true) ↔ (ret2 = true) :=
    Iff.trans h1 (Iff.symm h2)
  cases ret1 <;> cases ret2 <;> simp at h <;> simp
end Proof
