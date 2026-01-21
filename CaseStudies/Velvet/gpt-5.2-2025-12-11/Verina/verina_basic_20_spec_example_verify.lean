import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def distinctVals (arr : Array Int) : Finset Int :=
  arr.toList.toFinset



def distinctProduct (arr : Array Int) : Int :=
  (distinctVals arr).prod (fun x => x)



def precondition (arr : Array Int) : Prop :=
  True




def postcondition (arr : Array Int) (result : Int) : Prop :=
  result = distinctProduct arr


def test1_arr : Array Int := #[2, 3, 2, 4]

def test1_Expected : Int := 24

def test3_arr : Array Int := #[]

def test3_Expected : Int := 1

def test6_arr : Array Int := #[-1, -2, -1, -3]

def test6_Expected : Int := -6







section Proof
theorem test1_precondition : precondition test1_arr := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_arr test1_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test3_precondition : precondition test3_arr := by
    intros; expose_names; exact (trivial); done

theorem test3_postcondition : postcondition test3_arr test3_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test6_precondition : precondition test6_arr := by
    intros; expose_names; exact (trivial); done

theorem test6_postcondition : postcondition test6_arr test6_Expected := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness
    (arr : Array Int)
    : precondition arr →
  (∀ ret1 ret2,
    postcondition arr ret1 →
    postcondition arr ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  -- unfold postcondition in the hypotheses and finish by equality chaining
  dsimp [postcondition] at h1 h2
  exact Eq.trans h1 (Eq.symm h2)
end Proof
