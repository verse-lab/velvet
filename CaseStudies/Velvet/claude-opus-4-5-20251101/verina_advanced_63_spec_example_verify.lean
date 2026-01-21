import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isSortedNonDecreasing (nums : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < nums.length → nums[i]! ≤ nums[j]!



def precondition (nums : List Int) : Prop :=
  isSortedNonDecreasing nums






def postcondition (nums : List Int) (result : Nat) : Prop :=
  result = nums.toFinset.card


def test1_nums : List Int := [1, 1, 2]

def test1_Expected : Nat := 2

def test2_nums : List Int := [0, 0, 1, 1, 1, 2, 2, 3, 3, 4]

def test2_Expected : Nat := 5

def test6_nums : List Int := []

def test6_Expected : Nat := 0







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  unfold precondition isSortedNonDecreasing test1_nums
  intro i j hij hjlen
  -- We need to prove [1, 1, 2][i]! ≤ [1, 1, 2][j]! given i < j and j < 3
  -- Let's do case analysis manually
  match j, hjlen with
  | 0, h => omega  -- j = 0 contradicts i < j for natural i
  | 1, h => 
    match i, hij with
    | 0, _ => decide  -- [1,1,2][0]! ≤ [1,1,2][1]! is 1 ≤ 1
  | 2, h =>
    match i, hij with
    | 0, _ => decide  -- [1,1,2][0]! ≤ [1,1,2][2]! is 1 ≤ 2
    | 1, _ => decide  -- [1,1,2][1]! ≤ [1,1,2][2]! is 1 ≤ 2


theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test2

theorem test2_precondition :
  precondition test2_nums := by
  unfold precondition isSortedNonDecreasing test2_nums
  intro i j hij hjlen
  simp only [List.length] at hjlen
  match j with
  | 0 => omega
  | 1 => match i with | 0 => decide | _ + 1 => omega
  | 2 => match i with | 0 => decide | 1 => decide | _ + 2 => omega
  | 3 => match i with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => omega
  | 4 => match i with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | _ + 4 => omega
  | 5 => match i with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide | _ + 5 => omega
  | 6 => match i with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide | 5 => decide | _ + 6 => omega
  | 7 => match i with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide | 5 => decide | 6 => decide | _ + 7 => omega
  | 8 => match i with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide | 5 => decide | 6 => decide | 7 => decide | _ + 8 => omega
  | 9 => match i with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide | 5 => decide | 6 => decide | 7 => decide | 8 => decide | _ + 9 => omega
  | _ + 10 => omega


theorem test2_postcondition :
  postcondition test2_nums test2_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-- test6

theorem test6_precondition :
  precondition test6_nums := by
  unfold precondition isSortedNonDecreasing test6_nums
  intro i j hij hjlen
  simp at hjlen


theorem test6_postcondition :
  postcondition test6_nums test6_Expected := by
  intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

-----------------------------
-- Uniqueness Verification --
-----------------------------

theorem uniqueness (nums : List Int):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro _h_pre
  intro ret1 ret2 h1 h2
  unfold postcondition at h1 h2
  rw [h1, h2]
end Proof
