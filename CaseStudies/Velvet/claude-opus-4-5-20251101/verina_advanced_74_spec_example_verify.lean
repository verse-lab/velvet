import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def subarray (l : List Nat) (i : Nat) (j : Nat) : List Nat :=
  (l.drop i).take (j - i + 1)

def distinctCount (l : List Nat) : Nat :=
  l.toFinset.card

def squaredDistinctCount (l : List Nat) (i : Nat) (j : Nat) : Nat :=
  let sub := subarray l i j
  let d := distinctCount sub
  d * d



def precondition (nums : List Nat) :=
  1 ≤ nums.length ∧ nums.length ≤ 100 ∧ nums.all (fun x => 1 ≤ x ∧ x ≤ 100)





def postcondition (nums : List Nat) (result : Nat) :=
  result = (Finset.range nums.length).sum (fun i =>
           (Finset.Icc i (nums.length - 1)).sum (fun j =>
           squaredDistinctCount nums i j))


def test1_nums : List Nat := [1]

def test1_Expected : Nat := 1

def test3_nums : List Nat := [1, 2, 1]

def test3_Expected : Nat := 15

def test4_nums : List Nat := [1, 2, 3, 4]

def test4_Expected : Nat := 50







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  unfold precondition test1_nums
  native_decide


theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test3

theorem test3_precondition :
  precondition test3_nums := by
  unfold precondition test3_nums
  simp only [List.length]
  constructor
  · omega
  · constructor
    · omega
    · native_decide


theorem test3_postcondition :
  postcondition test3_nums test3_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test4

theorem test4_precondition :
  precondition test4_nums := by
  unfold precondition test4_nums
  native_decide


theorem test4_postcondition :
  postcondition test4_nums test4_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (nums : List Nat):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  rw [hpost1, hpost2]
end Proof
