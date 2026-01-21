import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isStrictlyIncreasing (l : List Int) : Prop :=
  l.Pairwise (· < ·)


def isStrictlyIncreasingSubseq (sub : List Int) (original : List Int) : Prop :=
  sub.Sublist original ∧ isStrictlyIncreasing sub



def ensures1 (nums : List Int) (result : Nat) : Prop :=
  ∃ sub : List Int, isStrictlyIncreasingSubseq sub nums ∧ sub.length = result


def ensures2 (nums : List Int) (result : Nat) : Prop :=
  ∀ sub : List Int, isStrictlyIncreasingSubseq sub nums → sub.length ≤ result

def precondition (nums : List Int) : Prop :=
  True

def postcondition (nums : List Int) (result : Nat) : Prop :=
  ensures1 nums result ∧ ensures2 nums result


def test1_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]

def test1_Expected : Nat := 4

def test3_nums : List Int := [7, 7, 7, 7, 7, 7, 7]

def test3_Expected : Nat := 1

def test4_nums : List Int := []

def test4_Expected : Nat := 0







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  intros; expose_names; exact (trivial); done
end Proof
