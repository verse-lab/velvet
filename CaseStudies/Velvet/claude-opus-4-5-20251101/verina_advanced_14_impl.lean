import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    ifPowerOfFour: Determine whether a natural number is a power of four
    Natural language breakdown:
    1. A natural number n is a power of four if there exists a natural number x such that n = 4^x
    2. Powers of four are: 1 (4^0), 4 (4^1), 16 (4^2), 64 (4^3), 256 (4^4), 1024 (4^5), ...
    3. 0 is NOT a power of four (there is no x such that 4^x = 0)
    4. 1 is a power of four (4^0 = 1)
    5. Numbers like 2, 3, 8, etc. are not powers of four
    6. The function returns true if n is a power of four, false otherwise
    
    Key observations:
    - 4^x is always positive for any natural x, so 0 is never a power of four
    - We need to check if n can be expressed as 4^x for some natural x
    - This is equivalent to checking if n = (2^2)^x = 2^(2x), i.e., n is a power of 2 with even exponent
-/

section Specs
-- Predicate: n is a power of four if there exists some natural x where 4^x = n
def isPowerOfFour (n : Nat) : Prop :=
  ∃ x : Nat, 4 ^ x = n

-- Postcondition: result is true iff n is a power of four
def ensures1 (n : Nat) (result : Bool) :=
  result = true ↔ isPowerOfFour n

def precondition (n : Nat) :=
  True  -- no preconditions

def postcondition (n : Nat) (result : Bool) :=
  ensures1 n result
end Specs

section Impl
method ifPowerOfFour (n: Nat)
  return (result: Bool)
  require precondition n
  ensures postcondition n result
  do
    if n = 0 then
      return false
    else
      let mut current := n
      while current > 1 ∧ current % 4 = 0
        -- Invariant 1: current is positive (we started with n > 0 and only divide)
        invariant "current_pos" current > 0
        -- Invariant 2: n is a power of 4 iff current is a power of 4
        -- Initialization: current = n, so trivially holds
        -- Preservation: if current = 4^k and current % 4 = 0, then current/4 = 4^(k-1)
        -- Sufficiency: when current = 1, isPowerOfFour current holds (4^0 = 1)
        invariant "power_preserved" (isPowerOfFour n ↔ isPowerOfFour current)
        done_with current = 1 ∨ current % 4 ≠ 0
      do
        current := current / 4
      return current = 1
end Impl

section TestCases
-- Test case 1: n = 0, not a power of four (no x such that 4^x = 0)
def test1_n : Nat := 0
def test1_Expected : Bool := false

-- Test case 2: n = 1, power of four (4^0 = 1)
def test2_n : Nat := 1
def test2_Expected : Bool := true

-- Test case 3: n = 2, not a power of four
def test3_n : Nat := 2
def test3_Expected : Bool := false

-- Test case 4: n = 4, power of four (4^1 = 4)
def test4_n : Nat := 4
def test4_Expected : Bool := true

-- Test case 5: n = 8, not a power of four (8 = 2^3, but not 4^x)
def test5_n : Nat := 8
def test5_Expected : Bool := false

-- Test case 6: n = 16, power of four (4^2 = 16)
def test6_n : Nat := 16
def test6_Expected : Bool := true

-- Test case 7: n = 64, power of four (4^3 = 64)
def test7_n : Nat := 64
def test7_Expected : Bool := true

-- Test case 8: n = 100, not a power of four
def test8_n : Nat := 100
def test8_Expected : Bool := false

-- Test case 9: n = 256, power of four (4^4 = 256)
def test9_n : Nat := 256
def test9_Expected : Bool := true

-- Test case 10: n = 1024, power of four (4^5 = 1024)
def test10_n : Nat := 1024
def test10_Expected : Bool := true

-- Recommend to validate: 2, 4, 6 (covers 4^0=1, 4^1=4, 4^2=16 - small but representative powers)
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((ifPowerOfFour test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((ifPowerOfFour test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((ifPowerOfFour test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((ifPowerOfFour test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((ifPowerOfFour test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((ifPowerOfFour test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((ifPowerOfFour test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((ifPowerOfFour test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((ifPowerOfFour test9_n).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((ifPowerOfFour test10_n).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 150, Column 0
-- Message: unsolved goals
-- n : ℕ
-- result : Bool
-- ⊢ Decidable (postcondition n result)
-- Line: prove_postcondition_decidable_for ifPowerOfFour
-- [ERROR] Line 152, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for ifPowerOfFour
-- prove_precondition_decidable_for ifPowerOfFour
-- prove_postcondition_decidable_for ifPowerOfFour
-- derive_tester_for ifPowerOfFour
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
--     let res := ifPowerOfFourTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct ifPowerOfFour by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (require_1 : precondition n)
    (if_pos : n = 0)
    : postcondition n false := by
    unfold postcondition ensures1 isPowerOfFour
    rw [if_pos]
    constructor
    · intro h
      exact False.elim (Bool.false_ne_true h)
    · intro ⟨x, hx⟩
      have h4pos : 0 < 4 := by decide
      have h1 : 1 ≤ 4 ^ x := Nat.one_le_pow x 4 h4pos
      omega

theorem goal_1
    (n : ℕ)
    (require_1 : precondition n)
    (if_neg : ¬n = 0)
    (current : ℕ)
    (invariant_power_preserved : isPowerOfFour n ↔ isPowerOfFour current)
    (a_1 : current % 4 = 0)
    (invariant_current_pos : 0 < current)
    (a : 1 < current)
    : isPowerOfFour n ↔ isPowerOfFour (current / 4) := by
    apply Iff.trans invariant_power_preserved
    constructor
    · -- Forward: isPowerOfFour current → isPowerOfFour (current / 4)
      intro ⟨x, hx⟩
      -- Since current > 1 and 4^0 = 1, we have x > 0
      have hx_pos : x > 0 := by
        by_contra h
        push_neg at h
        interval_cases x
        simp at hx
        omega
      -- So x = (x - 1) + 1
      obtain ⟨y, hy⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hx_pos)
      use y
      rw [hy] at hx
      rw [Nat.pow_succ] at hx
      -- hx : 4 ^ y * 4 = current
      have h4pos : (0 : ℕ) < 4 := by omega
      have : current / 4 = 4 ^ y := by
        rw [← hx]
        rw [Nat.mul_div_cancel _ h4pos]
      exact this.symm
    · -- Backward: isPowerOfFour (current / 4) → isPowerOfFour current
      intro ⟨x, hx⟩
      use x + 1
      have hdiv : 4 ∣ current := Nat.dvd_of_mod_eq_zero a_1
      rw [Nat.pow_succ]
      -- Goal: 4 ^ x * 4 = current
      have h1 : current = 4 * (current / 4) := (Nat.mul_div_cancel' hdiv).symm
      have h2 : current / 4 = 4 ^ x := hx.symm
      calc 4 ^ x * 4 = 4 * 4 ^ x := by ring
        _ = 4 * (current / 4) := by rw [h2]
        _ = current := Nat.mul_div_cancel' hdiv

theorem goal_2
    (n : ℕ)
    (require_1 : precondition n)
    (if_neg : ¬n = 0)
    (current : ℕ)
    (invariant_power_preserved : isPowerOfFour n ↔ isPowerOfFour current)
    (done_1 : current = 1 ∨ ¬current % 4 = 0)
    (invariant_current_pos : 0 < current)
    : postcondition n (decide (current = 1)) := by
    unfold postcondition ensures1
    rw [decide_eq_true_iff]
    rw [invariant_power_preserved]
    unfold isPowerOfFour
    constructor
    · -- Forward: current = 1 → ∃ x, 4^x = current
      intro h
      use 0
      simp [h]
    · -- Backward: ∃ x, 4^x = current → current = 1
      intro ⟨x, hx⟩
      cases done_1 with
      | inl h1 => exact h1
      | inr hmod =>
        -- current % 4 ≠ 0, but 4^x = current
        -- If x ≥ 1, then 4 | 4^x, so current % 4 = 0, contradiction
        -- So x = 0, meaning current = 1
        cases x with
        | zero => 
          simp at hx
          exact hx.symm
        | succ k =>
          -- 4^(k+1) = 4^k * 4, so 4 | 4^(k+1)
          exfalso
          apply hmod
          rw [← hx]
          have h4div : 4 ∣ 4 ^ (k + 1) := by
            calc 4 = 4 ^ 1 := by ring
              _ ∣ 4 ^ (k + 1) := Nat.pow_dvd_pow 4 (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
          exact Nat.mod_eq_zero_of_dvd h4div


prove_correct ifPowerOfFour by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n require_1 if_pos)
  exact (goal_1 n require_1 if_neg current invariant_power_preserved a_1 invariant_current_pos a)
  exact (goal_2 n require_1 if_neg current invariant_power_preserved done_1 invariant_current_pos)
end Proof
