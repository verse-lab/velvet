import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def tankAfterSteps (gas : List Int) (cost : List Int) (start : Nat) (steps : Nat) : Int :=
  match steps with
  | 0 => 0
  | k + 1 =>
    let prev := tankAfterSteps gas cost start k
    let idx := (start + k) % gas.length
    prev + gas[idx]! - cost[idx]!


def canCompleteFrom (gas : List Int) (cost : List Int) (start : Nat) : Prop :=
  ∀ k : Nat, k < gas.length → tankAfterSteps gas cost start (k + 1) ≥ 0

def isValidStart (gas : List Int) (cost : List Int) (idx : Nat) : Prop :=
  idx < gas.length ∧ canCompleteFrom gas cost idx



def require1 (gas : List Int) (cost : List Int) :=
  gas.length > 0

def require2 (gas : List Int) (cost : List Int) :=
  gas.length = cost.length

def precondition (gas : List Int) (cost : List Int) :=
  require1 gas cost ∧ require2 gas cost


def ensures1 (gas : List Int) (cost : List Int) (result : Int) :=
  result = -1 ∨ (result ≥ 0 ∧ result < gas.length)


def ensures2 (gas : List Int) (cost : List Int) (result : Int) :=
  result ≥ 0 → isValidStart gas cost result.toNat


def ensures3 (gas : List Int) (cost : List Int) (result : Int) :=
  result ≥ 0 → ∀ j : Nat, j < result.toNat → ¬isValidStart gas cost j


def ensures4 (gas : List Int) (cost : List Int) (result : Int) :=
  result = -1 → ∀ j : Nat, j < gas.length → ¬canCompleteFrom gas cost j

def postcondition (gas : List Int) (cost : List Int) (result : Int) :=
  ensures1 gas cost result ∧
  ensures2 gas cost result ∧
  ensures3 gas cost result ∧
  ensures4 gas cost result


def test1_gas : List Int := [1, 2, 3, 4, 5]

def test1_cost : List Int := [3, 4, 5, 1, 2]

def test1_Expected : Int := 3

def test2_gas : List Int := [2, 3, 4]

def test2_cost : List Int := [3, 4, 3]

def test2_Expected : Int := -1

def test5_gas : List Int := [1, 2, 3]

def test5_cost : List Int := [1, 2, 3]

def test5_Expected : Int := 0







section Proof
theorem test1_precondition :
  precondition test1_gas test1_cost := by
  unfold precondition require1 require2 test1_gas test1_cost
  native_decide

theorem test1_postcondition :
  postcondition test1_gas test1_cost test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 isValidStart canCompleteFrom
  unfold test1_gas test1_cost test1_Expected
  refine ⟨?_, ?_, ?_, ?_⟩
  · right; simp
  · intro _
    refine ⟨by simp, ?_⟩
    intro k hk
    simp only [List.length] at hk
    interval_cases k <;> native_decide
  · intro _ j hj
    simp only [Int.toNat] at hj
    intro ⟨_, hcan⟩
    have h0 := hcan 0 (by simp)
    simp only [tankAfterSteps, List.length] at h0
    interval_cases j <;> simp at h0
  · intro h; simp at h

theorem test2_precondition :
  precondition test2_gas test2_cost := by
  unfold precondition require1 require2 test2_gas test2_cost
  native_decide

theorem test2_postcondition :
  postcondition test2_gas test2_cost test2_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4
  unfold test2_gas test2_cost test2_Expected
  refine ⟨?_, ?_, ?_, ?_⟩
  · left; rfl
  · intro h; omega
  · intro h; omega
  · intro _
    intro j hj
    unfold canCompleteFrom
    push_neg
    simp only [List.length] at hj
    interval_cases j
    · -- j = 0: show tankAfterSteps fails at k = 0
      use 0
      constructor
      · simp [List.length]
      · native_decide
    · -- j = 1: show tankAfterSteps fails at k = 0
      use 0
      constructor
      · simp [List.length]
      · native_decide
    · -- j = 2: show tankAfterSteps fails at k = 2
      use 2
      constructor
      · simp [List.length]
      · native_decide

theorem test5_precondition :
  precondition test5_gas test5_cost := by
  unfold precondition require1 require2 test5_gas test5_cost
  native_decide

theorem test5_postcondition :
  postcondition test5_gas test5_cost test5_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4
  unfold test5_gas test5_cost test5_Expected
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ensures1: 0 = -1 ∨ (0 ≥ 0 ∧ 0 < 3)
    right
    constructor <;> native_decide
  · -- ensures2: 0 ≥ 0 → isValidStart [1,2,3] [1,2,3] 0
    intro _
    unfold isValidStart
    constructor
    · native_decide
    · unfold canCompleteFrom
      intro k hk
      simp only [List.length] at hk
      interval_cases k
      · unfold tankAfterSteps; native_decide
      · unfold tankAfterSteps; native_decide
      · unfold tankAfterSteps; native_decide
  · -- ensures3: 0 ≥ 0 → ∀ j < 0, ¬isValidStart ... j
    intro _ j hj
    omega
  · -- ensures4: 0 = -1 → ...
    intro h
    simp at h

theorem uniqueness (gas : List Int) (cost : List Int):
  precondition gas cost →
  (∀ ret1 ret2,
    postcondition gas cost ret1 →
    postcondition gas cost ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨e1_1, e2_1, e3_1, e4_1⟩ := hpost1
  obtain ⟨e1_2, e2_2, e3_2, e4_2⟩ := hpost2
  unfold ensures1 at e1_1 e1_2
  unfold ensures2 at e2_1 e2_2
  unfold ensures3 at e3_1 e3_2
  unfold ensures4 at e4_1 e4_2
  -- Case analysis on ret1 = -1 or ret1 ≥ 0
  rcases e1_1 with h1_neg | ⟨h1_nonneg, h1_lt⟩
  · -- Case: ret1 = -1
    rcases e1_2 with h2_neg | ⟨h2_nonneg, h2_lt⟩
    · -- Sub-case: ret2 = -1
      omega
    · -- Sub-case: ret2 ≥ 0
      have hvalid2 := e2_2 h2_nonneg
      unfold isValidStart at hvalid2
      obtain ⟨hidx2, hcan2⟩ := hvalid2
      have hcontra := e4_1 (by omega : ret1 = -1) ret2.toNat hidx2
      contradiction
  · -- Case: ret1 ≥ 0
    rcases e1_2 with h2_neg | ⟨h2_nonneg, h2_lt⟩
    · -- Sub-case: ret2 = -1
      have hvalid1 := e2_1 h1_nonneg
      unfold isValidStart at hvalid1
      obtain ⟨hidx1, hcan1⟩ := hvalid1
      have hcontra := e4_2 (by omega : ret2 = -1) ret1.toNat hidx1
      contradiction
    · -- Sub-case: ret2 ≥ 0, both are valid starts
      have hvalid1 := e2_1 h1_nonneg
      have hvalid2 := e2_2 h2_nonneg
      unfold isValidStart at hvalid1 hvalid2
      obtain ⟨hidx1, hcan1⟩ := hvalid1
      obtain ⟨hidx2, hcan2⟩ := hvalid2
      -- Use trichotomy on ret1 and ret2
      rcases Int.lt_trichotomy ret1 ret2 with hlt | heq | hgt
      · -- ret1 < ret2
        have h_toNat_lt : ret1.toNat < ret2.toNat := by
          have h1 : ret1.toNat = ret1 := by
            rw [Int.toNat_of_nonneg h1_nonneg]
          have h2 : ret2.toNat = ret2 := by
            rw [Int.toNat_of_nonneg h2_nonneg]
          omega
        have hnotvalid := e3_2 h2_nonneg ret1.toNat h_toNat_lt
        unfold isValidStart at hnotvalid
        push_neg at hnotvalid
        have := hnotvalid hidx1
        contradiction
      · exact heq
      · -- ret2 < ret1
        have h_toNat_lt : ret2.toNat < ret1.toNat := by
          have h1 : ret1.toNat = ret1 := by
            rw [Int.toNat_of_nonneg h1_nonneg]
          have h2 : ret2.toNat = ret2 := by
            rw [Int.toNat_of_nonneg h2_nonneg]
          omega
        have hnotvalid := e3_1 h1_nonneg ret2.toNat h_toNat_lt
        unfold isValidStart at hnotvalid
        push_neg at hnotvalid
        have := hnotvalid hidx2
        contradiction
end Proof
