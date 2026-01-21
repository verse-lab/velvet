import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def listMax (l : List Int) : Int :=
  l.foldl max 0

def maxLeft (heights : List Int) (i : Nat) : Int :=
  listMax (heights.take (i + 1))

def maxRight (heights : List Int) (i : Nat) : Int :=
  listMax (heights.drop i)

def waterAt (heights : List Int) (i : Nat) : Int :=
  let leftMax := maxLeft heights i
  let rightMax := maxRight heights i
  let waterLevel := min leftMax rightMax
  max (waterLevel - heights[i]!) 0


def allNonNegative (heights : List Int) : Prop :=
  ∀ i : Nat, i < heights.length → heights[i]! ≥ 0

def precondition (heights : List Int) :=
  allNonNegative heights





def postcondition (heights : List Int) (result : Int) :=
  result = ((List.range heights.length).map (waterAt heights)).foldl (· + ·) 0


def test1_heights : List Int := [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]

def test1_Expected : Int := 6

def test2_heights : List Int := [4, 2, 0, 3, 2, 5]

def test2_Expected : Int := 9

def test5_heights : List Int := [1, 10, 9, 11]

def test5_Expected : Int := 1







section Proof
theorem test1_precondition :
  precondition test1_heights := by
  unfold precondition allNonNegative test1_heights
  intro i hi
  simp only [List.length] at hi
  interval_cases i <;> native_decide


theorem test1_postcondition :
  postcondition test1_heights test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test2

theorem test2_precondition :
  precondition test2_heights := by
  unfold precondition allNonNegative test2_heights
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> native_decide


theorem test2_postcondition :
  postcondition test2_heights test2_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test5

theorem test5_precondition : precondition test5_heights := by
  unfold precondition allNonNegative test5_heights
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> native_decide


theorem test5_postcondition :
  postcondition test5_heights test5_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (heights : List Int):
  precondition heights →
  (∀ ret1 ret2,
    postcondition heights ret1 →
    postcondition heights ret2 →
    ret1 = ret2) := by
  intro _h_pre
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  rw [h1, h2]
end Proof
