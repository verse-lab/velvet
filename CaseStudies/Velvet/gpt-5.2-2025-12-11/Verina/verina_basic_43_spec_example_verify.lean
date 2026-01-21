import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def oddAt (k : Nat) : Nat := 2 * k + 1


def sumFourthOdd (n : Nat) : Nat :=
  (Finset.range n).sum (fun k => (oddAt k) ^ 4)



def precondition (n : Nat) : Prop :=
  True



def postcondition (n : Nat) (result : Nat) : Prop :=
  result = sumFourthOdd n


def test1_n : Nat := 0

def test1_Expected : Nat := 0

def test2_n : Nat := 1

def test2_Expected : Nat := 1

def test6_n : Nat := 5

def test6_Expected : Nat := 9669







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done


theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test2

theorem test2_precondition :
  precondition test2_n := by
  intros; expose_names; exact (trivial); done


theorem test2_postcondition :
  postcondition test2_n test2_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test6

theorem test6_precondition :
  precondition test6_n := by
  intros; expose_names; exact (trivial); done


theorem test6_postcondition :
  postcondition test6_n test6_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (n : Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _hp
  intro ret1 ret2 h1 h2
  simp [postcondition] at h1 h2
  exact h1.trans h2.symm
end Proof
