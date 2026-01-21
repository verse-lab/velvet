import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def subarraySum (xs : List Int) (i : Nat) (j : Nat) : Int :=
  (xs.drop i).take (j - i + 1) |>.foldl (· + ·) 0


def isValidSubarrayRange (xs : List Int) (i : Nat) (j : Nat) : Prop :=
  i ≤ j ∧ j < xs.length


def isAchievableSum (xs : List Int) (sum : Int) : Prop :=
  xs = [] ∧ sum = 0 ∨
  xs ≠ [] ∧ ∃ i j, isValidSubarrayRange xs i j ∧ subarraySum xs i j = sum


def isMaximalSum (xs : List Int) (sum : Int) : Prop :=
  ∀ i j, isValidSubarrayRange xs i j → subarraySum xs i j ≤ sum

def precondition (xs : List Int) :=
  True

def postcondition (xs : List Int) (result : Int) :=
  isAchievableSum xs result ∧ isMaximalSum xs result


def test1_xs : List Int := [1, -2, 3, 4, -1]

def test1_Expected : Int := 7

def test2_xs : List Int := [-2, -3, -1, -5]

def test2_Expected : Int := -1

def test4_xs : List Int := []

def test4_Expected : Int := 0







section Proof
theorem test1_precondition :
  precondition test1_xs := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_xs test1_Expected := by
  unfold postcondition isAchievableSum isMaximalSum isValidSubarrayRange subarraySum test1_xs test1_Expected
  constructor
  · right
    refine ⟨by decide, 2, 3, ?_, ?_⟩
    · simp only [List.length]; omega
    · native_decide
  · intro i j ⟨hij, hjlen⟩
    simp only [List.length] at hjlen
    have hi : i ≤ 4 := Nat.le_trans hij (Nat.lt_succ_iff.mp hjlen)
    have hj : j ≤ 4 := Nat.lt_succ_iff.mp hjlen
    interval_cases j <;> interval_cases i <;> native_decide

theorem test2_precondition :
  precondition test2_xs := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_xs test2_Expected := by
  unfold postcondition isAchievableSum isMaximalSum isValidSubarrayRange subarraySum test2_xs test2_Expected
  constructor
  · -- isAchievableSum: show -1 is achievable
    right
    constructor
    · decide
    · use 2, 2
      native_decide
  · -- isMaximalSum: show -1 is maximal
    intro i j ⟨hij, hjlen⟩
    simp only [List.length_cons, List.length_nil] at hjlen
    -- j < 4 and i ≤ j, so i < 4 and j < 4
    have hi : i < 4 := Nat.lt_of_le_of_lt hij hjlen
    -- Enumerate all possible cases for i and j
    match i, j with
    | 0, 0 => native_decide
    | 0, 1 => native_decide
    | 0, 2 => native_decide
    | 0, 3 => native_decide
    | 1, 0 => omega
    | 1, 1 => native_decide
    | 1, 2 => native_decide
    | 1, 3 => native_decide
    | 2, 0 => omega
    | 2, 1 => omega
    | 2, 2 => native_decide
    | 2, 3 => native_decide
    | 3, 0 => omega
    | 3, 1 => omega
    | 3, 2 => omega
    | 3, 3 => native_decide
    | i' + 4, _ => omega
    | _, j' + 4 => omega

theorem test4_precondition :
  precondition test4_xs := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_xs test4_Expected := by
  unfold postcondition test4_xs test4_Expected
  constructor
  · -- isAchievableSum [] 0
    unfold isAchievableSum
    left
    constructor
    · rfl
    · rfl
  · -- isMaximalSum [] 0
    unfold isMaximalSum
    intro i j h
    unfold isValidSubarrayRange at h
    simp only [List.length_nil] at h
    exact absurd h.2 (Nat.not_lt_zero j)

theorem uniqueness (xs : List Int):
  precondition xs →
  (∀ ret1 ret2,
    postcondition xs ret1 →
    postcondition xs ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨hach1, hmax1⟩ := hpost1
  obtain ⟨hach2, hmax2⟩ := hpost2
  unfold isAchievableSum at hach1 hach2
  unfold isMaximalSum at hmax1 hmax2
  -- Case analysis on whether xs is empty
  cases hach1 with
  | inl h1 =>
    -- xs = [] and ret1 = 0
    obtain ⟨hnil1, hret1_zero⟩ := h1
    cases hach2 with
    | inl h2 =>
      -- xs = [] and ret2 = 0
      obtain ⟨_, hret2_zero⟩ := h2
      rw [hret1_zero, hret2_zero]
    | inr h2 =>
      -- xs ≠ [] but we said xs = [], contradiction
      obtain ⟨hne2, _⟩ := h2
      exact absurd hnil1 hne2
  | inr h1 =>
    -- xs ≠ [] and there exist i1, j1 with sum ret1
    obtain ⟨hne1, i1, j1, hvalid1, hsum1⟩ := h1
    cases hach2 with
    | inl h2 =>
      -- xs = [] but we said xs ≠ [], contradiction
      obtain ⟨hnil2, _⟩ := h2
      exact absurd hnil2 hne1
    | inr h2 =>
      -- xs ≠ [] and there exist i2, j2 with sum ret2
      obtain ⟨_, i2, j2, hvalid2, hsum2⟩ := h2
      -- Show ret1 ≤ ret2: ret1 = subarraySum at (i1,j1), and hmax2 says all sums ≤ ret2
      have hle1 : ret1 ≤ ret2 := by
        have h := hmax2 i1 j1 hvalid1
        rw [hsum1] at h
        exact h
      -- Show ret2 ≤ ret1: ret2 = subarraySum at (i2,j2), and hmax1 says all sums ≤ ret1
      have hle2 : ret2 ≤ ret1 := by
        have h := hmax1 i2 j2 hvalid2
        rw [hsum2] at h
        exact h
      -- By antisymmetry
      exact Int.le_antisymm hle1 hle2
end Proof
