import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def shouldReplaceWithColon (c : Char) : Bool :=
  c = ' ' || c = ',' || c = '.'

def charSpecAt (s : String) (result : String) (i : Nat) : Prop :=
  i < s.toList.length →
    let cin := s.toList[i]!
    let cout := result.toList[i]!
    (shouldReplaceWithColon cin = true → cout = ':') ∧
    (shouldReplaceWithColon cin = false → cout = cin)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  result.toList.length = s.toList.length ∧
  ∀ i : Nat, charSpecAt s result i


def test1_s : String := "Hello, world. How are you?"

def test1_Expected : String := "Hello::world::How:are:you?"

def test3_s : String := ",. "

def test3_Expected : String := ":::"

def test8_s : String := "a, b.c"

def test8_Expected : String := "a::b:c"







section Proof
theorem test1_precondition : precondition test1_s := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_s test1_Expected := by
    sorry
end Proof
