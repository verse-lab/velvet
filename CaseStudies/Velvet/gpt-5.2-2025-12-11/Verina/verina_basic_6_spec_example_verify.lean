import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000







def precondition (a : Int) (b : Int) (c : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  (result ≤ a ∧ result ≤ b ∧ result ≤ c) ∧
  (result = a ∨ result = b ∨ result = c)


def test1_a : Int := 3

def test1_b : Int := 2

def test1_c : Int := 1

def test1_Expected : Int := 1

def test5_a : Int := 2

def test5_b : Int := -3

def test5_c : Int := 4

def test5_Expected : Int := -3

def test9_a : Int := -5

def test9_b : Int := -2

def test9_c : Int := -3

def test9_Expected : Int := -5







section Proof
theorem test1_precondition :
  precondition test1_a test1_b test1_c := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_b test1_c test1_Expected := by
  simp [postcondition, test1_a, test1_b, test1_c, test1_Expected]

theorem test5_precondition :
  precondition test5_a test5_b test5_c := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition :
  postcondition test5_a test5_b test5_c test5_Expected := by
  simp [postcondition, test5_a, test5_b, test5_c, test5_Expected]

theorem test9_precondition :
  precondition test9_a test9_b test9_c := by
  intros; expose_names; exact (trivial); done

theorem test9_postcondition :
  postcondition test9_a test9_b test9_c test9_Expected := by
  simp [postcondition, test9_a, test9_b, test9_c, test9_Expected]
end Proof
