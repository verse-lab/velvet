import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def intCube (x : Int) : Int := x * x * x

def precondition (a : Array Int) : Prop :=
  True




def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
    (∀ (i : Nat), i < a.size → result[i]! = intCube (a[i]!))


def test1_a : Array Int := #[1, 2, 3, 4]

def test1_Expected : Array Int := #[1, 8, 27, 64]

def test2_a : Array Int := #[0, -1, -2, 3]

def test2_Expected : Array Int := #[0, -1, -8, 27]

def test3_a : Array Int := #[]

def test3_Expected : Array Int := #[]







section Proof
theorem test1_precondition :
  precondition test1_a := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_Expected := by
  unfold postcondition
  constructor
  · simp [test1_a, test1_Expected]
  · intro i hi
    -- First reduce `a.size` to `4`, then `omega` can case-split `i < 4`.
    have hi4 : i < 4 := by
      simpa [test1_a] using hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      omega
    rcases hi' with rfl | rfl | rfl | rfl
    · simp [test1_a, test1_Expected, intCube]
    · simp [test1_a, test1_Expected, intCube]
    · simp [test1_a, test1_Expected, intCube]
    · simp [test1_a, test1_Expected, intCube]

theorem test2_precondition :
  precondition test2_a := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_a test2_Expected := by
  unfold postcondition
  constructor
  · simp [test2_a, test2_Expected]
  · intro i hi
    have hi' : i < 4 := by simpa [test2_a] using hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst h0
      simp [test2_a, test2_Expected, intCube]
    · subst h1
      simp [test2_a, test2_Expected, intCube]
    · subst h2
      simp [test2_a, test2_Expected, intCube]
    · subst h3
      simp [test2_a, test2_Expected, intCube]

theorem test3_precondition :
  precondition test3_a := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_a test3_Expected := by
  unfold postcondition
  constructor
  · simp [test3_a, test3_Expected]
  · intro i hi
    exfalso
    exact (Nat.not_lt_zero i) (by simpa [test3_a] using hi)
end Proof
