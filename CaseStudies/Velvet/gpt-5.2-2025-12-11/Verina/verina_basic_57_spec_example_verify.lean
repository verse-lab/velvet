import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def countLessThanSpec (numbers : Array Int) (threshold : Int) : Nat :=
  (numbers.toList.countP (fun x => x < threshold))



def precondition (numbers : Array Int) (threshold : Int) : Prop :=
  True




def postcondition (numbers : Array Int) (threshold : Int) (result : Nat) : Prop :=
  result = countLessThanSpec numbers threshold


def test1_numbers : Array Int := #[1, 2, 3, 4, 5]

def test1_threshold : Int := 3

def test1_Expected : Nat := 2

def test3_numbers : Array Int := #[-1, 0, 1]

def test3_threshold : Int := 0

def test3_Expected : Nat := 1

def test4_numbers : Array Int := #[5, 6, 7, 2, 1]

def test4_threshold : Int := 5

def test4_Expected : Nat := 2







section Proof
theorem test1_precondition : precondition test1_numbers test1_threshold := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_numbers test1_threshold test1_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test3_precondition : precondition test3_numbers test3_threshold := by
    intros; expose_names; exact (trivial); done

theorem test3_postcondition : postcondition test3_numbers test3_threshold test3_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test4_precondition : precondition test4_numbers test4_threshold := by
    intros; expose_names; exact (trivial); done

theorem test4_postcondition : postcondition test4_numbers test4_threshold test4_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness
    (numbers : Array Int)
    (threshold : Int)
    : precondition numbers threshold →
  (∀ ret1 ret2,
    postcondition numbers threshold ret1 →
    postcondition numbers threshold ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  -- Unfold postcondition: ret1 = spec and ret2 = spec
  -- Then ret1 = ret2 follows by rewriting.
  simp [postcondition] at h1 h2
  -- h1 : ret1 = countLessThanSpec numbers threshold
  -- h2 : ret2 = countLessThanSpec numbers threshold
  simpa [h1, h2]
end Proof
