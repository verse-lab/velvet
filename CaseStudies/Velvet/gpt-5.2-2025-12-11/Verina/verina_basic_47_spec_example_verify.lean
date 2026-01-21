import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000









def precondition (a : Array Int) : Prop :=
  a.size > 0




def postcondition (a : Array Int) (result : Int) : Prop :=
  result = a.sum


def test1_a : Array Int := #[1, 2, 3, 4, 5]

def test1_Expected : Int := 15

def test3_a : Array Int := #[-1, -2, -3]

def test3_Expected : Int := -6

def test4_a : Array Int := #[10, -10]

def test4_Expected : Int := 0







section Proof
theorem test1_precondition : precondition test1_a := by
  simp [precondition, test1_a]

theorem test1_postcondition : postcondition test1_a test1_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test3_precondition : precondition test3_a := by
  simp [precondition, test3_a]

theorem test3_postcondition : postcondition test3_a test3_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test4_precondition : precondition test4_a := by
  simp [precondition, test4_a]

theorem test4_postcondition : postcondition test4_a test4_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness
    (a : Array Int)
    : precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  simp [postcondition] at h1 h2
  exact Eq.trans h1 (Eq.symm h2)
end Proof
