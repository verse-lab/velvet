import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (n : Nat) : Prop :=
  True






def postcondition (n : Nat) (result : Nat) : Prop :=
  result = n % 10 ∧ result < 10


def test1_n : Nat := 123

def test1_Expected : Nat := 3

def test2_n : Nat := 0

def test2_Expected : Nat := 0

def test4_n : Nat := 10

def test4_Expected : Nat := 0







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition
  simp [test1_n, test1_Expected]

theorem test2_precondition :
  precondition test2_n := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_n test2_Expected := by
  simp [postcondition, test2_n, test2_Expected]

theorem test4_precondition :
  precondition test4_n := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_n test4_Expected := by
  simp [postcondition, test4_n, test4_Expected, Nat.mod_self]

theorem uniqueness (n : Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _hn
  intro ret1 ret2 h1 h2
  -- unfold postcondition in the hypotheses and use the shared equality to `n % 10`
  have h1' : ret1 = n % 10 := (show ret1 = n % 10 ∧ ret1 < 10 from by simpa [postcondition] using h1).1
  have h2' : ret2 = n % 10 := (show ret2 = n % 10 ∧ ret2 < 10 from by simpa [postcondition] using h2).1
  exact Eq.trans h1' (Eq.symm h2')
end Proof
