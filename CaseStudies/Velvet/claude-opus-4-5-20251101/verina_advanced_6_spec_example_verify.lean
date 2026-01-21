import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def vowels : List Char := ['a', 'e', 'i', 'o', 'u']



def precondition (s : String) : Prop :=
  True




def postcondition (s : String) (result : Bool) : Prop :=
  result = (vowels.all (fun v => v ∈ s.toLower.toList))


def test1_s : String := "education"

def test1_Expected : Bool := true

def test3_s : String := "AEIOU"

def test3_Expected : Bool := true

def test4_s : String := "hello"

def test4_Expected : Bool := false







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition test1_s test1_Expected vowels
  native_decide

theorem test3_precondition :
  precondition test3_s := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
  unfold postcondition test3_s test3_Expected vowels
  native_decide

theorem test4_precondition :
  precondition test4_s := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_s test4_Expected := by
  simp only [postcondition, test4_s, test4_Expected, vowels]
  native_decide

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  rw [h1, h2]
end Proof
