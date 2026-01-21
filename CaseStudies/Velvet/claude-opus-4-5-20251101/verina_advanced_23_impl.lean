import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isPowerOfTwo: Determine whether a given integer is a power of two
    Natural language breakdown:
    1. We have an input integer n
    2. An integer n is a power of two if there exists a non-negative integer x such that n = 2^x
    3. The function should return true if n is a power of two, false otherwise
    4. Negative numbers are not powers of two (return false)
    5. Zero is not a power of two (return false)
    6. The value 1 is a power of two (2^0 = 1)
    7. Examples of powers of two: 1, 2, 4, 8, 16, 32, 64, ...
    8. Examples of non-powers of two: 0, 3, 5, 6, 7, 9, 10, ...

    Property-oriented specification:
    - If result is true: n is positive and there exists a natural number x such that n = 2^x
    - If result is false: either n <= 0 or there is no natural number x such that n = 2^x
    - This can be expressed as: result = true ↔ (n > 0 ∧ ∃ x : Nat, n = 2^x)
-/

section Specs
-- Helper Functions

-- Predicate: check if an integer is a power of two
-- n is a power of two if n > 0 and there exists a natural number x such that n = 2^x
def isPowerOfTwoProp (n : Int) : Prop :=
  n > 0 ∧ ∃ x : Nat, n = (2 : Int) ^ x

-- Postcondition clauses
def ensures1 (n : Int) (result : Bool) :=
  result = true ↔ isPowerOfTwoProp n

def precondition (n : Int) :=
  True  -- no preconditions

def postcondition (n : Int) (result : Bool) :=
  ensures1 n result
end Specs

section Impl
method isPowerOfTwo (n : Int)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  if n <= 0 then
    return false
  else
    let mut val := n
    while val > 1 ∧ val % 2 = 0
      -- Invariant 1: val stays positive throughout the loop
      -- Init: val = n and n > 0 (from else branch)
      -- Pres: val > 1 and val % 2 = 0 implies val / 2 > 0
      invariant "val_positive" val > 0
      -- Invariant 2: n is a power of two iff val is a power of two
      -- Init: val = n, so trivially holds
      -- Pres: dividing an even number by 2 preserves power-of-two property
      -- Suff: at exit, val = 1 means isPowerOfTwoProp val, or val % 2 ≠ 0 means not
      invariant "power_of_two_preserved" (isPowerOfTwoProp n ↔ isPowerOfTwoProp val)
      done_with (val = 1 ∨ val % 2 ≠ 0)
    do
      val := val / 2
    if val = 1 then
      return true
    else
      return false
end Impl

section TestCases
-- Test case 1: n = 1, which is 2^0 (power of two)
def test1_n : Int := 1
def test1_Expected : Bool := true

-- Test case 2: n = 16, which is 2^4 (power of two)
def test2_n : Int := 16
def test2_Expected : Bool := true

-- Test case 3: n = 3, not a power of two
def test3_n : Int := 3
def test3_Expected : Bool := false

-- Test case 4: n = 0, not a power of two (zero case)
def test4_n : Int := 0
def test4_Expected : Bool := false

-- Test case 5: n = -2, negative number (not a power of two)
def test5_n : Int := -2
def test5_Expected : Bool := false

-- Test case 6: n = 8, which is 2^3 (power of two)
def test6_n : Int := 8
def test6_Expected : Bool := true

-- Test case 7: n = 10, not a power of two
def test7_n : Int := 10
def test7_Expected : Bool := false

-- Test case 8: n = 2, which is 2^1 (power of two)
def test8_n : Int := 2
def test8_Expected : Bool := true

-- Test case 9: n = 64, which is 2^6 (power of two)
def test9_n : Int := 64
def test9_Expected : Bool := true

-- Test case 10: n = -16, negative power of two base (not a power of two)
def test10_n : Int := -16
def test10_Expected : Bool := false

-- Recommend to validate: 1, 2, 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((isPowerOfTwo test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isPowerOfTwo test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isPowerOfTwo test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isPowerOfTwo test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isPowerOfTwo test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isPowerOfTwo test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isPowerOfTwo test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isPowerOfTwo test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isPowerOfTwo test9_n).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((isPowerOfTwo test10_n).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 158, Column 0
-- Message: unsolved goals
-- n : ℤ
-- result : Bool
-- ⊢ Decidable (postcondition n result)
-- Line: prove_postcondition_decidable_for isPowerOfTwo
-- [ERROR] Line 160, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for isPowerOfTwo
-- prove_precondition_decidable_for isPowerOfTwo
-- prove_postcondition_decidable_for isPowerOfTwo
-- derive_tester_for isPowerOfTwo
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Int)
--     let res := isPowerOfTwoTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isPowerOfTwo by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℤ)
    (require_1 : precondition n)
    (if_pos : n ≤ 0)
    : postcondition n false := by
    unfold postcondition ensures1 isPowerOfTwoProp
    rw [Bool.false_eq_true]
    apply iff_of_false
    · exact fun h => h
    · intro ⟨h_pos, _⟩
      omega

theorem goal_1
    (n : ℤ)
    (require_1 : precondition n)
    (val : ℤ)
    (invariant_power_of_two_preserved : isPowerOfTwoProp n ↔ isPowerOfTwoProp val)
    (if_neg : 0 < n)
    (invariant_val_positive : 0 < val)
    (a : 1 < val)
    (a_1 : 2 ∣ val)
    : isPowerOfTwoProp n ↔ isPowerOfTwoProp (val / 2) := by
    rw [invariant_power_of_two_preserved]
    unfold isPowerOfTwoProp
    constructor
    · intro ⟨hpos, x, hx⟩
      constructor
      · apply Int.ediv_pos_of_pos_of_dvd hpos (by omega : (0 : ℤ) ≤ 2) a_1
      · cases x with
        | zero => 
          simp at hx
          omega
        | succ k =>
          use k
          rw [hx]
          have h2ne : (2 : ℤ) ≠ 0 := by omega
          rw [pow_succ]
          rw [mul_comm]
          rw [Int.mul_ediv_cancel_left _ h2ne]
    · intro ⟨hpos, x, hx⟩
      constructor
      · exact invariant_val_positive
      · use x + 1
        have h2ne : (2 : ℤ) ≠ 0 := by omega
        rw [pow_succ]
        have : val = 2 * (val / 2) := by
          rw [mul_comm]
          exact (Int.ediv_mul_cancel a_1).symm
        rw [this, hx]
        ring

theorem goal_2
    (n : ℤ)
    (require_1 : precondition n)
    (val : ℤ)
    (invariant_power_of_two_preserved : isPowerOfTwoProp n ↔ isPowerOfTwoProp val)
    (if_pos : val = 1)
    (if_neg : 0 < n)
    (invariant_val_positive : 0 < val)
    (done_1 : val = 1 ∨ val % 2 = 1)
    : postcondition n true := by
    unfold postcondition ensures1
    constructor
    · intro _
      rw [invariant_power_of_two_preserved]
      unfold isPowerOfTwoProp
      rw [if_pos]
      constructor
      · exact Int.one_pos
      · use 0
        simp [Int.pow_zero]
    · intro _
      rfl

theorem goal_3
    (n : ℤ)
    (require_1 : precondition n)
    (val : ℤ)
    (invariant_power_of_two_preserved : isPowerOfTwoProp n ↔ isPowerOfTwoProp val)
    (if_neg_1 : ¬val = 1)
    (if_neg : 0 < n)
    (invariant_val_positive : 0 < val)
    (done_1 : val = 1 ∨ val % 2 = 1)
    : postcondition n false := by
    unfold postcondition ensures1
    rw [Bool.false_eq_true]
    -- Now we need to prove: False ↔ isPowerOfTwoProp n
    -- This is equivalent to showing ¬isPowerOfTwoProp n
    apply iff_of_false
    · exact fun h => h
    · -- Need to show ¬isPowerOfTwoProp n
      -- First show ¬isPowerOfTwoProp val, then use the invariant
      have val_odd : val % 2 = 1 := Or.resolve_left done_1 if_neg_1
      have not_pow_val : ¬isPowerOfTwoProp val := by
        intro ⟨hpos, x, hx⟩
        -- val = 2^x where x : Nat
        cases x with
        | zero =>
          -- val = 2^0 = 1, contradicts if_neg_1
          simp at hx
          exact if_neg_1 hx
        | succ k =>
          -- val = 2^(k+1) = 2 * 2^k, so val is even
          have : val % 2 = 0 := by
            rw [hx]
            have : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
            rw [this]
            simp [Int.mul_emod_right]
          omega
      -- Use the invariant to transfer to n
      rw [invariant_power_of_two_preserved]
      exact not_pow_val


prove_correct isPowerOfTwo by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n require_1 if_pos)
  exact (goal_1 n require_1 val invariant_power_of_two_preserved if_neg invariant_val_positive a a_1)
  exact (goal_2 n require_1 val invariant_power_of_two_preserved if_pos if_neg invariant_val_positive done_1)
  exact (goal_3 n require_1 val invariant_power_of_two_preserved if_neg_1 if_neg invariant_val_positive done_1)
end Proof
