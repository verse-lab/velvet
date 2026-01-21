import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isItEight: Return true if the input n is divisible by 8 or has 8 as one of its digits
    Natural language breakdown:
    1. We have an integer input n (can be positive, negative, or zero)
    2. The function should return true if n is divisible by 8 (n mod 8 = 0)
    3. The function should also return true if the digit 8 appears anywhere in the decimal representation of n
    4. For negative numbers, we consider the absolute value when checking for digit 8
    5. The two conditions are connected by OR - either condition being true makes the result true
    6. Zero is divisible by 8, so it returns true
    7. Examples:
       - 8: divisible by 8 AND contains digit 8 → true
       - 98: not divisible by 8, but contains digit 8 → true
       - 1224: divisible by 8 (1224 = 153 × 8), no digit 8 → true
       - 73: not divisible by 8, no digit 8 → false
       - -123456780: contains digit 8 → true
-/

section Specs
-- Mathematical definition: a natural number has digit 8 if there exists some
-- position k such that the k-th digit (from the right, 0-indexed) equals 8
def hasDigit8 (n : Nat) : Prop :=
  ∃ k : Nat, (n / (10^k)) % 10 = 8

-- Postcondition: result is true iff n is divisible by 8 or contains digit 8
def ensures1 (n : Int) (result : Bool) :=
  result = true ↔ (n % 8 = 0 ∨ hasDigit8 (Int.natAbs n))

def precondition (n : Int) :=
  True  -- no preconditions

def postcondition (n : Int) (result : Bool) :=
  ensures1 n result
end Specs

section Impl
method isItEight (n : Int)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  -- Check divisibility by 8
  if n % 8 = 0 then
    return true
  else
    -- Check if any digit is 8
    let mut absN := Int.natAbs n
    let mut found := false
    while absN > 0
      -- Invariant 1: The relationship between found, absN, and original number
      -- If original has digit 8, either found is true or digit 8 is still in absN
      -- Initialization: absN = Int.natAbs n, found = false, so trivially holds
      -- Preservation: When we find 8, set found=true; otherwise digit 8 (if any) remains in absN/10
      -- Sufficiency: At exit (absN=0), hasDigit8 0 is false, so hasDigit8 original ↔ found
      invariant "digit8_tracking" hasDigit8 (Int.natAbs n) ↔ (found = true ∨ hasDigit8 absN)
      done_with (absN = 0)
    do
      let digit := absN % 10
      if digit = 8 then
        found := true
      absN := absN / 10
    return found
end Impl

section TestCases
-- Test case 1: n = 8 (both divisible by 8 and contains 8)
def test1_n : Int := 8
def test1_Expected : Bool := true

-- Test case 2: n = 98 (not divisible by 8, but contains 8)
def test2_n : Int := 98
def test2_Expected : Bool := true

-- Test case 3: n = 1224 (divisible by 8, no digit 8)
def test3_n : Int := 1224
def test3_Expected : Bool := true

-- Test case 4: n = 73 (neither divisible by 8 nor contains 8)
def test4_n : Int := 73
def test4_Expected : Bool := false

-- Test case 5: n = 208 (divisible by 8 and contains 8)
def test5_n : Int := 208
def test5_Expected : Bool := true

-- Test case 6: n = 0 (divisible by 8)
def test6_n : Int := 0
def test6_Expected : Bool := true

-- Test case 7: n = -123456780 (negative, contains 8)
def test7_n : Int := -123456780
def test7_Expected : Bool := true

-- Test case 8: n = 1 (neither condition)
def test8_n : Int := 1
def test8_Expected : Bool := false

-- Test case 9: n = -9999 (negative, neither condition)
def test9_n : Int := -9999
def test9_Expected : Bool := false

-- Test case 10: n = -123453 (negative, neither condition)
def test10_n : Int := -123453
def test10_Expected : Bool := false

-- Recommend to validate: 1, 3, 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((isItEight test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isItEight test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isItEight test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isItEight test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isItEight test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isItEight test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isItEight test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isItEight test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isItEight test9_n).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((isItEight test10_n).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 158, Column 0
-- Message: unsolved goals
-- n : ℤ
-- result : Bool
-- ⊢ Decidable (postcondition n result)
-- Line: prove_postcondition_decidable_for isItEight
-- [ERROR] Line 160, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for isItEight
-- prove_precondition_decidable_for isItEight
-- prove_postcondition_decidable_for isItEight
-- derive_tester_for isItEight
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Int)
--     let res := isItEightTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isItEight by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℤ)
    (require_1 : precondition n)
    (if_pos : 8 ∣ n)
    : postcondition n true := by
    unfold postcondition ensures1
    constructor
    · intro _
      left
      exact Int.emod_eq_zero_of_dvd if_pos
    · intro _
      rfl

theorem goal_1
    (n : ℤ)
    (require_1 : precondition n)
    (absN : ℕ)
    (found : Bool)
    (invariant_digit8_tracking : hasDigit8 n.natAbs ↔ found = true ∨ hasDigit8 absN)
    (if_pos_1 : absN % 10 = 8)
    (if_neg : ¬8 ∣ n)
    (if_pos : 0 < absN)
    : hasDigit8 n.natAbs := by
    -- First prove hasDigit8 absN using k = 0
    have h_digit8_absN : hasDigit8 absN := by
      unfold hasDigit8
      use 0
      simp [Nat.pow_zero, Nat.div_one]
      exact if_pos_1
    -- Use the invariant to conclude hasDigit8 n.natAbs
    exact invariant_digit8_tracking.mpr (Or.inr h_digit8_absN)

theorem goal_2
    (n : ℤ)
    (require_1 : precondition n)
    (absN : ℕ)
    (found : Bool)
    (invariant_digit8_tracking : hasDigit8 n.natAbs ↔ found = true ∨ hasDigit8 absN)
    (if_neg_1 : ¬absN % 10 = 8)
    (if_neg : ¬8 ∣ n)
    (if_pos : 0 < absN)
    : hasDigit8 n.natAbs ↔ found = true ∨ hasDigit8 (absN / 10) := by
    -- Key lemma: hasDigit8 absN ↔ hasDigit8 (absN / 10) when absN % 10 ≠ 8
    have key : hasDigit8 absN ↔ hasDigit8 (absN / 10) := by
      constructor
      · -- Forward: hasDigit8 absN → hasDigit8 (absN / 10)
        intro ⟨k, hk⟩
        -- k cannot be 0 because absN % 10 ≠ 8
        cases k with
        | zero =>
          simp at hk
          exact absurd hk if_neg_1
        | succ j =>
          use j
          -- (absN / 10^(j+1)) % 10 = 8
          -- 10^(j+1) = 10^j * 10
          have h1 : 10 ^ (j + 1) = 10 ^ j * 10 := Nat.pow_succ 10 j
          rw [h1] at hk
          -- hk : absN / (10^j * 10) % 10 = 8
          -- Need: (absN / 10) / 10^j % 10 = 8
          -- Use: m / n / k = m / (n * k), so absN / 10 / 10^j = absN / (10 * 10^j)
          have h2 : absN / 10 / (10 ^ j) = absN / (10 * 10 ^ j) := Nat.div_div_eq_div_mul absN 10 (10^j)
          rw [h2]
          -- Now need absN / (10 * 10^j) = absN / (10^j * 10)
          have h3 : 10 * 10 ^ j = 10 ^ j * 10 := Nat.mul_comm 10 (10^j)
          rw [h3]
          exact hk
      · -- Backward: hasDigit8 (absN / 10) → hasDigit8 absN
        intro ⟨k, hk⟩
        use k + 1
        -- hk : (absN / 10) / 10^k % 10 = 8
        -- Need: absN / 10^(k+1) % 10 = 8
        have h1 : 10 ^ (k + 1) = 10 ^ k * 10 := Nat.pow_succ 10 k
        rw [h1]
        -- Need: absN / (10^k * 10) % 10 = 8
        have h2 : absN / 10 / (10 ^ k) = absN / (10 * 10 ^ k) := Nat.div_div_eq_div_mul absN 10 (10^k)
        have h3 : 10 * 10 ^ k = 10 ^ k * 10 := Nat.mul_comm 10 (10^k)
        rw [← h3, ← h2]
        exact hk
    -- Now use the invariant and the key lemma
    rw [invariant_digit8_tracking]
    constructor
    · intro h
      cases h with
      | inl hf => left; exact hf
      | inr hd => right; exact key.mp hd
    · intro h
      cases h with
      | inl hf => left; exact hf
      | inr hd => right; exact key.mpr hd

theorem goal_3
    (n : ℤ)
    (require_1 : precondition n)
    (absN : ℕ)
    (found : Bool)
    (invariant_digit8_tracking : hasDigit8 n.natAbs ↔ found = true ∨ hasDigit8 absN)
    (done_1 : absN = 0)
    (i : ℕ)
    (found_1 : Bool)
    (if_neg : ¬8 ∣ n)
    (i_1 : absN = i ∧ found = found_1)
    : postcondition n found_1 := by
    unfold postcondition ensures1
    -- First, show that hasDigit8 0 is false
    have hasDigit8_zero_false : ¬hasDigit8 0 := by
      intro ⟨k, hk⟩
      simp [Nat.zero_div, Nat.zero_mod] at hk
    -- From i_1, extract found = found_1
    have found_eq : found = found_1 := i_1.2
    -- Substitute absN = 0 into the invariant
    rw [done_1] at invariant_digit8_tracking
    -- Simplify the invariant using hasDigit8 0 being false
    have inv_simplified : hasDigit8 n.natAbs ↔ found_1 = true := by
      rw [← found_eq]
      constructor
      · intro h
        have h2 := invariant_digit8_tracking.mp h
        cases h2 with
        | inl h => exact h
        | inr h => exact absurd h hasDigit8_zero_false
      · intro h
        apply invariant_digit8_tracking.mpr
        left
        exact h
    -- Handle the divisibility condition
    have not_div8 : ¬(n % 8 = 0) := by
      intro h
      apply if_neg
      exact Int.dvd_of_emod_eq_zero h
    -- Prove the biconditional
    constructor
    · intro hfound
      right
      exact inv_simplified.mpr hfound
    · intro h
      cases h with
      | inl h => exact absurd h not_div8
      | inr h => exact inv_simplified.mp h


prove_correct isItEight by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n require_1 if_pos)
  exact (goal_1 n require_1 absN found invariant_digit8_tracking if_pos_1 if_neg if_pos)
  exact (goal_2 n require_1 absN found invariant_digit8_tracking if_neg_1 if_neg if_pos)
  exact (goal_3 n require_1 absN found invariant_digit8_tracking done_1 i found_1 if_neg i_1)
end Proof
