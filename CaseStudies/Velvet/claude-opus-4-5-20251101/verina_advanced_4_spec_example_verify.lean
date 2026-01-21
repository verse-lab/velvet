import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def isStrictlyIncreasing (sub : List Int) : Prop :=
  List.Chain' (· < ·) sub



def isIncreasingSubseqOf (sub : List Int) (arr : Array Int) : Prop :=
  sub.Sublist arr.toList ∧ isStrictlyIncreasing sub



def precondition (a : Array Int) : Prop :=
  True






def postcondition (a : Array Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ sub : List Int, isIncreasingSubseqOf sub a ∧ sub.length = result.toNat) ∧
  (∀ sub : List Int, isIncreasingSubseqOf sub a → sub.length ≤ result.toNat)


def test1_a : Array Int := #[5, 2, 8, 6, 3, 6, 9, 7]

def test1_Expected : Int := 4

def test6_a : Array Int := #[]

def test6_Expected : Int := 0

def test8_a : Array Int := #[1, 2, 3, 4, 5]

def test8_Expected : Int := 5







section Proof
theorem test1_precondition :
  precondition test1_a := by
  intros; expose_names; exact (trivial); done
end Proof
