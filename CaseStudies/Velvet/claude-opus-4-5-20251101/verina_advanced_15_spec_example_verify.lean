import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def hasIncreasingTriplet (nums : List Int) : Prop :=
  ∃ i j k : Nat, i < j ∧ j < k ∧ k < nums.length ∧
    nums[i]! < nums[j]! ∧ nums[j]! < nums[k]!



def ensures1 (nums : List Int) (result : Bool) :=
  result = true ↔ hasIncreasingTriplet nums

def precondition (nums : List Int) :=
  True

def postcondition (nums : List Int) (result : Bool) :=
  ensures1 nums result


def test1_nums : List Int := [1, 2, 3]

def test1_Expected : Bool := true

def test2_nums : List Int := [5, 4, 3, 2, 1]

def test2_Expected : Bool := false

def test3_nums : List Int := [2, 1, 5, 0, 4, 6]

def test3_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition ensures1 test1_nums test1_Expected hasIncreasingTriplet
  constructor
  · intro _
    use 0, 1, 2
    native_decide
  · intro _
    rfl

theorem test2_precondition :
  precondition test2_nums := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_nums test2_Expected := by
  unfold postcondition ensures1 test2_nums test2_Expected
  simp only [Bool.false_eq_true, false_iff]
  unfold hasIncreasingTriplet
  push_neg
  intro i j k hi_lt_j hj_lt_k hk_lt_len
  simp only [test2_nums, List.length] at hk_lt_len ⊢
  have hi : i < 5 := by omega
  have hj : j < 5 := by omega
  have hk : k < 5 := hk_lt_len
  rcases i with _ | _ | _ | _ | _ <;> rcases j with _ | _ | _ | _ | _ <;> rcases k with _ | _ | _ | _ | _ <;>
    simp_all <;> omega

theorem test3_precondition :
  precondition test3_nums := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_nums test3_Expected := by
  unfold postcondition ensures1 test3_nums test3_Expected hasIncreasingTriplet
  constructor
  · intro _
    use 3, 4, 5
    native_decide
  · intro _
    rfl

theorem uniqueness (nums : List Int):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro _
  intro ret1 ret2 h1 h2
  -- h1 : ret1 = true ↔ hasIncreasingTriplet nums
  -- h2 : ret2 = true ↔ hasIncreasingTriplet nums
  -- We need: ret1 = ret2
  unfold postcondition ensures1 at h1 h2
  -- Use Bool.eq_iff_iff: a = b ↔ (a = true ↔ b = true)
  rw [Bool.eq_iff_iff]
  -- Now we need: (ret1 = true ↔ ret2 = true)
  -- From h1: ret1 = true ↔ hasIncreasingTriplet nums
  -- From h2: ret2 = true ↔ hasIncreasingTriplet nums
  -- So ret1 = true ↔ ret2 = true by transitivity through hasIncreasingTriplet nums
  exact h1.trans h2.symm
end Proof
