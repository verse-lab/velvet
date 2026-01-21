import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def allBinaryDigits (digits : List Nat) : Prop :=
  ∀ d ∈ digits, d = 0 ∨ d = 1



def precondition (digits : List Nat) :=
  allBinaryDigits digits





def postcondition (digits : List Nat) (result : Nat) :=



  (digits.length = 0 → result = 0) ∧
  (∀ i : Nat, i < digits.length → 
    result.testBit (digits.length - 1 - i) = (digits[i]! == 1)) ∧
  (∀ j : Nat, j ≥ digits.length → result.testBit j = false)


def test1_digits : List Nat := [1, 0, 1]

def test1_Expected : Nat := 5

def test2_digits : List Nat := [1, 1, 1, 1]

def test2_Expected : Nat := 15

def test5_digits : List Nat := []

def test5_Expected : Nat := 0







section Proof
theorem test1_precondition :
  precondition test1_digits := by
  unfold precondition allBinaryDigits test1_digits
  intro d hd
  simp only [List.mem_cons, List.mem_nil_iff] at hd
  rcases hd with rfl | rfl | rfl | h
  · right; rfl
  · left; rfl
  · right; rfl
  · exact False.elim h

theorem test1_postcondition :
  postcondition test1_digits test1_Expected := by
  unfold postcondition test1_digits test1_Expected
  constructor
  · intro h
    simp at h
  constructor
  · intro i hi
    simp only [List.length] at hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | n + 3 => omega
  · intro j hj
    simp only [List.length] at hj
    match j with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => native_decide
    | 4 => native_decide
    | 5 => native_decide
    | 6 => native_decide
    | 7 => native_decide
    | 8 => native_decide
    | 9 => native_decide
    | 10 => native_decide
    | n + 11 => 
      have h1 : 5 < 2 ^ (n + 11) := by
        have : 2 ^ (n + 11) ≥ 2 ^ 11 := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 11 ≤ n + 11)
        omega
      exact Nat.testBit_lt_two_pow h1

theorem test2_precondition :
  precondition test2_digits := by
  unfold precondition allBinaryDigits test2_digits
  intro d hd
  simp only [List.mem_cons, List.mem_nil_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl | hfalse
  · right; rfl
  · right; rfl
  · right; rfl
  · right; rfl
  · exact False.elim hfalse

theorem test2_postcondition :
  postcondition test2_digits test2_Expected := by
  unfold postcondition test2_digits test2_Expected
  constructor
  · -- First part: length = 0 → result = 0 (vacuously true)
    intro h
    simp at h
  constructor
  · -- Second part: ∀ i < 4, 15.testBit (3 - i) = (digits[i]! == 1)
    intro i hi
    simp only [List.length] at hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | 3 => native_decide
    | n + 4 => omega
  · -- Third part: ∀ j ≥ 4, 15.testBit j = false
    intro j hj
    simp only [List.length] at hj
    match j with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
    | 4 => native_decide
    | 5 => native_decide
    | 6 => native_decide
    | 7 => native_decide
    | n + 8 =>
      have h1 : 15 < 2 ^ (n + 8) := by
        have : 2 ^ 4 ≤ 2 ^ (n + 8) := by
          apply Nat.pow_le_pow_right
          · omega
          · omega
        omega
      exact Nat.testBit_lt_two_pow h1

theorem test5_precondition :
  precondition test5_digits := by
  simp [precondition, allBinaryDigits, test5_digits, List.not_mem_nil]

theorem test5_postcondition :
  postcondition test5_digits test5_Expected := by
  unfold postcondition test5_digits test5_Expected
  constructor
  · -- First conjunct: [].length = 0 → 0 = 0
    intro _
    rfl
  constructor
  · -- Second conjunct: ∀ i, i < 0 → ... (vacuously true)
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · -- Third conjunct: ∀ j, j ≥ 0 → (0 : Nat).testBit j = false
    intro j _
    exact Nat.zero_testBit j

theorem uniqueness (digits : List Nat):
  precondition digits →
  (∀ ret1 ret2,
    postcondition digits ret1 →
    postcondition digits ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  apply Nat.eq_of_testBit_eq
  intro j
  -- Case split on whether j < digits.length or j ≥ digits.length
  by_cases hj : j < digits.length
  · -- Case: j < digits.length
    -- We need to find i such that j = digits.length - 1 - i
    -- Let i = digits.length - 1 - j
    have hi : digits.length - 1 - j < digits.length := by omega
    have hj_eq : j = digits.length - 1 - (digits.length - 1 - j) := by omega
    -- Get the bit conditions from postconditions
    obtain ⟨_, hbits1, _⟩ := hpost1
    obtain ⟨_, hbits2, _⟩ := hpost2
    have h1 := hbits1 (digits.length - 1 - j) hi
    have h2 := hbits2 (digits.length - 1 - j) hi
    rw [hj_eq]
    rw [h1, h2]
  · -- Case: j ≥ digits.length
    push_neg at hj
    obtain ⟨_, _, hhigh1⟩ := hpost1
    obtain ⟨_, _, hhigh2⟩ := hpost2
    rw [hhigh1 j hj, hhigh2 j hj]
end Proof
