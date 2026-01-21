import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def InArray (a : Array Int) (v : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = v

def IsMinOfArray (a : Array Int) (mn : Int) : Prop :=
  InArray a mn ∧ (∀ (i : Nat), i < a.size → mn ≤ a[i]!)

def IsMaxOfArray (a : Array Int) (mx : Int) : Prop :=
  InArray a mx ∧ (∀ (i : Nat), i < a.size → a[i]! ≤ mx)




def precondition (a : Array Int) : Prop :=
  a.size ≠ 0





def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (mn : Int) (mx : Int),
    IsMinOfArray a mn ∧
    IsMaxOfArray a mx ∧
    result = mx - mn


def test1_a : Array Int := #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

def test1_Expected : Int := 8

def test4_a : Array Int := #[7]

def test4_Expected : Int := 0

def test6_a : Array Int := #[1, -1, 2, -2]

def test6_Expected : Int := 4







section Proof
theorem test1_precondition :
  precondition test1_a := by
  unfold precondition
  simp [test1_a]

theorem test1_postcondition :
  postcondition test1_a test1_Expected := by
  unfold postcondition
  refine ⟨(1 : Int), (9 : Int), ?_, ?_, ?_⟩
  · -- IsMinOfArray test1_a 1
    unfold IsMinOfArray InArray
    constructor
    · -- InArray test1_a 1
      refine ⟨1, ?_, ?_⟩
      · simp [test1_a]
      · simp [test1_a]
    · -- ∀ i, i < size → 1 ≤ a[i]!
      intro i hi
      have hi' : i < 11 := by simpa [test1_a] using hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by
        omega
      rcases this with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [test1_a]
  · -- IsMaxOfArray test1_a 9
    unfold IsMaxOfArray InArray
    constructor
    · -- InArray test1_a 9
      refine ⟨5, ?_, ?_⟩
      · simp [test1_a]
      · simp [test1_a]
    · -- ∀ i, i < size → a[i]! ≤ 9
      intro i hi
      have hi' : i < 11 := by simpa [test1_a] using hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by
        omega
      rcases this with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [test1_a]
  · -- result = mx - mn
    simp [test1_Expected]

theorem test4_precondition :
  precondition test4_a := by
  simp [precondition, test4_a]

theorem test4_postcondition :
  postcondition test4_a test4_Expected := by
  unfold postcondition
  refine ⟨(7 : Int), (7 : Int), ?_, ?_, ?_⟩
  · -- IsMinOfArray test4_a 7
    unfold IsMinOfArray
    constructor
    · -- InArray test4_a 7
      unfold InArray
      refine ⟨0, ?_, ?_⟩ <;> simp [test4_a]
    · intro i hi
      have : i = 0 := (Nat.lt_one_iff.mp (by simpa [test4_a] using hi))
      subst this
      simp [test4_a]
  · -- IsMaxOfArray test4_a 7
    unfold IsMaxOfArray
    constructor
    · -- InArray test4_a 7
      unfold InArray
      refine ⟨0, ?_, ?_⟩ <;> simp [test4_a]
    · intro i hi
      have : i = 0 := (Nat.lt_one_iff.mp (by simpa [test4_a] using hi))
      subst this
      simp [test4_a]
  · -- result = mx - mn
    simp [test4_Expected, Int.sub_self]

theorem test6_precondition :
  precondition test6_a := by
  simp [precondition, test6_a]

theorem test6_postcondition :
  postcondition test6_a test6_Expected := by
  unfold postcondition
  refine ⟨(-2 : Int), (2 : Int), ?_, ?_, ?_⟩
  · -- IsMinOfArray
    unfold IsMinOfArray
    constructor
    · -- InArray
      unfold InArray
      refine ⟨3, ?_, ?_⟩
      · simp [test6_a]
      · simp [test6_a]
    · intro i hi
      -- show -2 ≤ test6_a[i]!
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
        have hi' : i < 4 := by simpa [test6_a] using hi
        omega
      rcases this with rfl | rfl | rfl | rfl
      · simp [test6_a]
      · simp [test6_a]
      · simp [test6_a]
      · simp [test6_a]
  · -- IsMaxOfArray
    unfold IsMaxOfArray
    constructor
    · -- InArray
      unfold InArray
      refine ⟨2, ?_, ?_⟩
      · simp [test6_a]
      · simp [test6_a]
    · intro i hi
      -- show test6_a[i]! ≤ 2
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
        have hi' : i < 4 := by simpa [test6_a] using hi
        omega
      rcases this with rfl | rfl | rfl | rfl
      · simp [test6_a]
      · simp [test6_a]
      · simp [test6_a]
      · simp [test6_a]
  · -- result = mx - mn
    simp [test6_Expected]

theorem uniqueness (a : Array Int) :
  precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨mn1, mx1, hmin1, hmax1, hret1⟩
  rcases hpost2 with ⟨mn2, mx2, hmin2, hmax2, hret2⟩

  -- Unpack min/max specs
  rcases hmin1 with ⟨hinmn1, hmn1_le⟩
  rcases hmin2 with ⟨hinmn2, hmn2_le⟩
  rcases hmax1 with ⟨hinmx1, hle_mx1⟩
  rcases hmax2 with ⟨hinmx2, hle_mx2⟩

  -- Uniqueness of minimum
  have hmn1_le_mn2 : mn1 ≤ mn2 := by
    rcases hinmn2 with ⟨i, hi, hai⟩
    have : mn1 ≤ a[i]! := hmn1_le i hi
    simpa [hai] using this
  have hmn2_le_mn1 : mn2 ≤ mn1 := by
    rcases hinmn1 with ⟨i, hi, hai⟩
    have : mn2 ≤ a[i]! := hmn2_le i hi
    simpa [hai] using this
  have hmn : mn1 = mn2 := le_antisymm hmn1_le_mn2 hmn2_le_mn1

  -- Uniqueness of maximum
  have hmx1_le_mx2 : mx1 ≤ mx2 := by
    rcases hinmx1 with ⟨i, hi, hai⟩
    have : a[i]! ≤ mx2 := hle_mx2 i hi
    -- rewrite a[i]! = mx1
    simpa [hai] using this
  have hmx2_le_mx1 : mx2 ≤ mx1 := by
    rcases hinmx2 with ⟨i, hi, hai⟩
    have : a[i]! ≤ mx1 := hle_mx1 i hi
    simpa [hai] using this
  have hmx : mx1 = mx2 := le_antisymm hmx1_le_mx2 hmx2_le_mx1

  -- Conclude ret1 = ret2
  calc
    ret1 = mx1 - mn1 := by simpa [hret1]
    _ = mx2 - mn2 := by simpa [hmx, hmn]
    _ = ret2 := by simpa [hret2]
end Proof
