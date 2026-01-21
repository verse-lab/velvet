import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def leftMax (height : List Nat) (i : Nat) : Nat :=
  (height.take (i + 1)).foldl max 0


def rightMax (height : List Nat) (i : Nat) : Nat :=
  (height.drop i).foldl max 0



def precondition (height : List Nat) :=
  True







def postcondition (height : List Nat) (result : Nat) :=
  result = (Finset.range height.length).sum (fun i =>
    let waterLevel := min (leftMax height i) (rightMax height i)
    let h := if i < height.length then height[i]! else 0
    if waterLevel > h then waterLevel - h else 0)


def test1_height : List Nat := [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]

def test1_Expected : Nat := 6

def test2_height : List Nat := [4, 2, 0, 3, 2, 5]

def test2_Expected : Nat := 9

def test3_height : List Nat := [1, 0, 2]

def test3_Expected : Nat := 1







section Proof
theorem test1_precondition :
  precondition test1_height := by
  intros; expose_names; exact (trivial); done


theorem test1_postcondition :
  postcondition test1_height test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test2

theorem test2_precondition :
  precondition test2_height := by
  intros; expose_names; exact (trivial); done


theorem test2_postcondition :
  postcondition test2_height test2_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test3

theorem test3_precondition :
  precondition test3_height := by
  intros; expose_names; exact (trivial); done


theorem test3_postcondition :
  postcondition test3_height test3_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (height : List Nat):
  precondition height →
  (∀ ret1 ret2,
    postcondition height ret1 →
    postcondition height ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  rw [h1, h2]
end Proof
