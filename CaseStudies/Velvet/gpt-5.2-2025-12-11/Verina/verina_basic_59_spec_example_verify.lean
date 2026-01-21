import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000

def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : Int × Int) : Prop :=
  result.1 = (2 : Int) * x ∧
  result.2 = (4 : Int) * x


def test1_x : Int := 0

def test1_Expected : (Int × Int) := (0, 0)

def test2_x : Int := 1

def test2_Expected : (Int × Int) := (2, 4)

def test3_x : Int := -1

def test3_Expected : (Int × Int) := (-2, -4)







section Proof
theorem test1_precondition : precondition test1_x := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_x test1_Expected := by
  simp [postcondition, test1_x, test1_Expected]

theorem test2_precondition : precondition test2_x := by
    intros; expose_names; exact (trivial); done

theorem test2_postcondition : postcondition test2_x test2_Expected := by
  simp [postcondition, test2_x, test2_Expected]

theorem test3_precondition : precondition test3_x := by
    intros; expose_names; exact (trivial); done

theorem test3_postcondition : postcondition test3_x test3_Expected := by
  simp [postcondition, test3_x, test3_Expected]

theorem uniqueness
    (x : Int)
    : precondition x →
  (∀ ret1 ret2,
    postcondition x ret1 →
    postcondition x ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨h11, h12⟩
  rcases hpost2 with ⟨h21, h22⟩
  apply Prod.ext
  · exact Eq.trans h11 (Eq.symm h21)
  · exact Eq.trans h12 (Eq.symm h22)
end Proof
