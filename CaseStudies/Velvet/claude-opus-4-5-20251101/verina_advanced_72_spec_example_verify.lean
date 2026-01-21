import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def singleDigitPrimes : List Nat := [2, 3, 5, 7]



def precondition (n : Nat) : Prop :=
  True



def postcondition (n : Nat) (result : Nat) : Prop :=

  (result = 0 ↔ n ≤ 1 ∨ ∀ p ∈ singleDigitPrimes, ¬(p ∣ n)) ∧

  (result ≠ 0 → (result ∈ singleDigitPrimes ∧ result ∣ n ∧ 
    ∀ p ∈ singleDigitPrimes, p ∣ n → result ≤ p))


def test1_n : Nat := 0

def test1_Expected : Nat := 0

def test2_n : Nat := 98

def test2_Expected : Nat := 2

def test6_n : Nat := 161

def test6_Expected : Nat := 7







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  unfold postcondition test1_n test1_Expected singleDigitPrimes
  constructor
  · -- First part: (0 = 0 ↔ 0 ≤ 1 ∨ ∀ p ∈ [2, 3, 5, 7], ¬(p ∣ 0))
    constructor
    · -- Forward: 0 = 0 → 0 ≤ 1 ∨ ...
      intro _
      left
      omega
    · -- Backward: 0 ≤ 1 ∨ ... → 0 = 0
      intro _
      rfl
  · -- Second part: 0 ≠ 0 → ...
    intro h
    exact absurd rfl h

theorem test2_precondition :
  precondition test2_n := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_n test2_Expected := by
  unfold postcondition test2_n test2_Expected singleDigitPrimes
  constructor
  · -- Part 1: (2 = 0 ↔ 98 ≤ 1 ∨ ∀ p ∈ [2, 3, 5, 7], ¬(p ∣ 98))
    constructor
    · intro h; omega
    · intro h
      cases h with
      | inl h1 => omega
      | inr h2 => 
        have : ¬(2 ∣ 98) := h2 2 (by simp)
        have : (2 ∣ 98) := by decide
        contradiction
  · -- Part 2: 2 ≠ 0 → (2 ∈ [2, 3, 5, 7] ∧ 2 ∣ 98 ∧ ∀ p ∈ [2, 3, 5, 7], p ∣ 98 → 2 ≤ p)
    intro _
    constructor
    · simp
    · constructor
      · decide
      · intro p hp hdiv
        simp at hp
        rcases hp with rfl | rfl | rfl | rfl
        · omega
        · have : ¬(3 ∣ 98) := by decide
          contradiction
        · have : ¬(5 ∣ 98) := by decide
          contradiction
        · omega

theorem test6_precondition :
  precondition test6_n := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_n test6_Expected := by
  unfold postcondition test6_n test6_Expected singleDigitPrimes
  constructor
  · -- Part 1: (7 = 0 ↔ 161 ≤ 1 ∨ ∀ p ∈ [2, 3, 5, 7], ¬(p ∣ 161))
    constructor
    · -- Forward: 7 = 0 → ...
      intro h
      omega
    · -- Backward: ... → 7 = 0
      intro h
      cases h with
      | inl h1 => omega
      | inr h2 =>
        -- 7 ∣ 161, so ¬(7 ∣ 161) is false
        have hdiv : (7 : Nat) ∣ 161 := by decide
        have hmem : 7 ∈ [2, 3, 5, 7] := by simp
        have hnotdiv : ¬(7 ∣ 161) := h2 7 hmem
        exact absurd hdiv hnotdiv
  · -- Part 2: 7 ≠ 0 → ...
    intro _
    constructor
    · -- 7 ∈ [2, 3, 5, 7]
      simp
    constructor
    · -- 7 ∣ 161
      decide
    · -- ∀ p ∈ [2, 3, 5, 7], p ∣ 161 → 7 ≤ p
      intro p hp hdiv
      simp at hp
      rcases hp with rfl | rfl | rfl | rfl
      · -- p = 2
        have : ¬(2 ∣ 161) := by decide
        exact absurd hdiv this
      · -- p = 3
        have : ¬(3 ∣ 161) := by decide
        exact absurd hdiv this
      · -- p = 5
        have : ¬(5 ∣ 161) := by decide
        exact absurd hdiv this
      · -- p = 7
        omega

theorem uniqueness (n : Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨h1_iff, h1_nonzero⟩ := hpost1
  obtain ⟨h2_iff, h2_nonzero⟩ := hpost2
  by_cases hr1 : ret1 = 0
  · -- ret1 = 0
    by_cases hr2 : ret2 = 0
    · -- ret2 = 0
      rw [hr1, hr2]
    · -- ret2 ≠ 0
      have h2_props := h2_nonzero hr2
      obtain ⟨h2_mem, h2_dvd, _⟩ := h2_props
      -- ret1 = 0 means n ≤ 1 or no single-digit prime divides n
      have h1_cond : n ≤ 1 ∨ ∀ p ∈ singleDigitPrimes, ¬(p ∣ n) := h1_iff.mp hr1
      cases h1_cond with
      | inl hle1 =>
        -- n ≤ 1 means n = 0 or n = 1
        interval_cases n
        · -- n = 0: but ret2 ≠ 0 and ret2 ∣ 0, need to check postcondition
          -- Actually for n = 0, the iff says ret2 = 0 ↔ 0 ≤ 1 ∨ ...
          -- 0 ≤ 1 is true, so ret2 = 0 ↔ True, meaning ret2 = 0
          have : ret2 = 0 := h2_iff.mpr (Or.inl (Nat.zero_le 1))
          contradiction
        · -- n = 1
          have : ret2 = 0 := h2_iff.mpr (Or.inl (Nat.le_refl 1))
          contradiction
      | inr hno_div =>
        -- No single-digit prime divides n, but ret2 ∈ singleDigitPrimes and ret2 ∣ n
        have := hno_div ret2 h2_mem
        contradiction
  · -- ret1 ≠ 0
    by_cases hr2 : ret2 = 0
    · -- ret2 = 0 but ret1 ≠ 0
      have h1_props := h1_nonzero hr1
      obtain ⟨h1_mem, h1_dvd, _⟩ := h1_props
      have h2_cond : n ≤ 1 ∨ ∀ p ∈ singleDigitPrimes, ¬(p ∣ n) := h2_iff.mp hr2
      cases h2_cond with
      | inl hle1 =>
        interval_cases n
        · have : ret1 = 0 := h1_iff.mpr (Or.inl (Nat.zero_le 1))
          contradiction
        · have : ret1 = 0 := h1_iff.mpr (Or.inl (Nat.le_refl 1))
          contradiction
      | inr hno_div =>
        have := hno_div ret1 h1_mem
        contradiction
    · -- Both ret1 ≠ 0 and ret2 ≠ 0
      have h1_props := h1_nonzero hr1
      have h2_props := h2_nonzero hr2
      obtain ⟨h1_mem, h1_dvd, h1_min⟩ := h1_props
      obtain ⟨h2_mem, h2_dvd, h2_min⟩ := h2_props
      -- ret1 is smallest, ret2 divides n and is in list, so ret1 ≤ ret2
      have hle1 : ret1 ≤ ret2 := h1_min ret2 h2_mem h2_dvd
      -- ret2 is smallest, ret1 divides n and is in list, so ret2 ≤ ret1
      have hle2 : ret2 ≤ ret1 := h2_min ret1 h1_mem h1_dvd
      exact Nat.le_antisymm hle1 hle2
end Proof
