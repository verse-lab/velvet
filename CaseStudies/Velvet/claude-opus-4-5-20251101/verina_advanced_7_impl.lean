import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- binaryToDecimal: Convert a binary number represented as a list of digits (0 or 1)
-- into its corresponding decimal value.
--
-- Natural language breakdown:
-- 1. Input is a list of natural numbers representing binary digits (each 0 or 1)
-- 2. The list is in big-endian format (most significant digit first)
-- 3. For a list of length n, the digit at position i (0-indexed from left) contributes:
--    digit[i] * 2^(n-1-i) to the total value
-- 4. Empty list should return 0
-- 5. Precondition: all digits must be either 0 or 1
-- 6. The result is uniquely determined by summing all positional contributions

section Specs
-- Check if all elements in the list are valid binary digits (0 or 1)
def allBinaryDigits (digits : List Nat) : Prop :=
  ∀ d ∈ digits, d = 0 ∨ d = 1

-- Precondition: all digits must be 0 or 1
def precondition (digits : List Nat) :=
  allBinaryDigits digits

-- Postcondition: the result equals the decimal interpretation of the binary list
-- Each digit at position i contributes digit[i] * 2^(n-1-i) to the result
-- Using testBit to characterize the result: bit position j in result equals digit at position (n-1-j)
def postcondition (digits : List Nat) (result : Nat) :=
  -- The result must satisfy the positional value property:
  -- For a binary number, each bit at position i from left contributes digit * 2^(n-1-i)
  -- This is equivalent to saying the result is bounded and matches the weighted sum
  (digits.length = 0 → result = 0) ∧
  (∀ i : Nat, i < digits.length → 
    result.testBit (digits.length - 1 - i) = (digits[i]! == 1)) ∧
  (∀ j : Nat, j ≥ digits.length → result.testBit j = false)
end Specs

section Impl
method binaryToDecimal (digits : List Nat)
  return (result : Nat)
  require precondition digits
  ensures postcondition digits result
  do
  let mut result := 0
  let mut i := 0
  let n := digits.length
  while i < n
    -- Invariant 1: Loop counter bounds
    -- Init: i = 0, so 0 ≤ 0 ∧ 0 ≤ n holds
    -- Preservation: i increments by 1, stays ≤ n due to loop condition
    -- Sufficiency: At exit i = n
    invariant "i_bounds" 0 ≤ i ∧ i ≤ n
    -- Invariant 2: n is the list length (constant)
    -- Init: n = digits.length at assignment
    -- Preservation: n is not modified in loop
    -- Sufficiency: Needed to connect n to digits.length in postcondition
    invariant "n_def" n = digits.length
    -- Invariant 3: Bits in result for positions 0 to i-1 match digits
    -- Init: i = 0, so vacuously true
    -- Preservation: After result := result * 2 + digit, bits shift and new bit added
    -- Sufficiency: At i = n, this gives the postcondition's bit matching property
    invariant "bits_match" ∀ j : Nat, j < i → result.testBit (i - 1 - j) = (digits[j]! == 1)
    -- Invariant 4: Upper bits (at position i and above) are zero
    -- Init: result = 0, all bits are false
    -- Preservation: result * 2 + digit where digit ∈ {0,1} keeps upper bits zero
    -- Sufficiency: At exit, combined with i = n gives upper bits condition
    invariant "upper_bits_zero" ∀ k : Nat, k ≥ i → result.testBit k = false
    done_with i = n
  do
    let digit := digits[i]!
    result := result * 2 + digit
    i := i + 1
  return result
end Impl

section TestCases
-- Test case 1: [1, 0, 1] -> 5 (example from problem: 1*4 + 0*2 + 1*1 = 5)
def test1_digits : List Nat := [1, 0, 1]
def test1_Expected : Nat := 5

-- Test case 2: [1, 1, 1, 1] -> 15 (8 + 4 + 2 + 1 = 15)
def test2_digits : List Nat := [1, 1, 1, 1]
def test2_Expected : Nat := 15

-- Test case 3: [0, 0, 0] -> 0 (all zeros)
def test3_digits : List Nat := [0, 0, 0]
def test3_Expected : Nat := 0

-- Test case 4: [1, 0, 0, 0, 0] -> 16 (2^4 = 16)
def test4_digits : List Nat := [1, 0, 0, 0, 0]
def test4_Expected : Nat := 16

-- Test case 5: [] -> 0 (empty list edge case)
def test5_digits : List Nat := []
def test5_Expected : Nat := 0

-- Test case 6: [1] -> 1 (single bit)
def test6_digits : List Nat := [1]
def test6_Expected : Nat := 1

-- Test case 7: [0] -> 0 (single zero bit)
def test7_digits : List Nat := [0]
def test7_Expected : Nat := 0

-- Test case 8: [1, 0, 1, 0] -> 10 (8 + 0 + 2 + 0 = 10)
def test8_digits : List Nat := [1, 0, 1, 0]
def test8_Expected : Nat := 10

-- Test case 9: [0, 1, 1] -> 3 (leading zero: 0*4 + 1*2 + 1*1 = 3)
def test9_digits : List Nat := [0, 1, 1]
def test9_Expected : Nat := 3

-- Recommend to validate: 1, 2, 5
-- Test 1: Example from problem description (must include)
-- Test 2: All ones case, good coverage
-- Test 5: Empty list edge case
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((binaryToDecimal test1_digits).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((binaryToDecimal test2_digits).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((binaryToDecimal test3_digits).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((binaryToDecimal test4_digits).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((binaryToDecimal test5_digits).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((binaryToDecimal test6_digits).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((binaryToDecimal test7_digits).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((binaryToDecimal test8_digits).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((binaryToDecimal test9_digits).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 148, Column 0
-- Message: unsolved goals
-- case refine_2.refine_2
-- digits : List ℕ
-- result : ℕ
-- ⊢ Decidable (∀ j ≥ digits.length, result.testBit j = false)
-- Line: prove_postcondition_decidable_for binaryToDecimal
-- [ERROR] Line 150, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for binaryToDecimal
-- prove_precondition_decidable_for binaryToDecimal
-- prove_postcondition_decidable_for binaryToDecimal
-- derive_tester_for binaryToDecimal
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (List Nat)
--     let res := binaryToDecimalTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct binaryToDecimal by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1 := by
    -- unfold precondition and allBinaryDigits
    unfold precondition at require_1
    unfold allBinaryDigits at require_1
    -- Since i < digits.length, digits[i]? = some digits[i]
    have h_eq : digits[i]? = some digits[i] := List.getElem?_eq_getElem if_pos
    -- So digits[i]?.getD 0 = digits[i]
    simp only [h_eq, Option.getD_some]
    -- digits[i] ∈ digits
    have h_mem : digits[i] ∈ digits := List.getElem_mem if_pos
    -- Apply the precondition
    exact require_1 digits[i] h_mem

theorem goal_0_1
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    : digits[i]?.getD 0 < 2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0_2
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    : result * 2 = result <<< 1 := by
    rw [Nat.shiftLeft_eq]

theorem goal_0_3
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    (h_mul_two_eq_shiftLeft : result * 2 = result <<< 1)
    : (result * 2).testBit 0 = false := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0_4
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    (h_mul_two_eq_shiftLeft : result * 2 = result <<< 1)
    (h_testBit_mul_two_zero : True)
    : ∀ (k : ℕ), (result * 2).testBit (k + 1) = result.testBit k := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0_5
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    (h_mul_two_eq_shiftLeft : result * 2 = result <<< 1)
    (h_testBit_mul_two_succ : ∀ (k : ℕ), (result * 2).testBit (k + 1) = result.testBit k)
    (h_testBit_mul_two_zero : True)
    : decide (digits[i]?.getD 0 % 2 = 1) = (digits[i]?.getD 0 == 1) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0_6
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    (h_mul_two_eq_shiftLeft : result * 2 = result <<< 1)
    (h_testBit_mul_two_succ : ∀ (k : ℕ), (result * 2).testBit (k + 1) = result.testBit k)
    (h_testBit_mul_two_zero : True)
    (h_testBit_add_small_zero : decide (digits[i]?.getD 0 % 2 = 1) = (digits[i]?.getD 0 == 1))
    : ∀ (k : ℕ), (result * 2 + digits[i]?.getD 0).testBit (k + 1) = result.testBit k := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0_7
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    (h_mul_two_eq_shiftLeft : result * 2 = result <<< 1)
    (h_testBit_mul_two_succ : ∀ (k : ℕ), (result * 2).testBit (k + 1) = result.testBit k)
    (h_testBit_add_small_succ : ∀ (k : ℕ), (result * 2 + digits[i]?.getD 0).testBit (k + 1) = result.testBit k)
    (h_testBit_mul_two_zero : True)
    (h_testBit_add_small_zero : decide (digits[i]?.getD 0 % 2 = 1) = (digits[i]?.getD 0 == 1))
    (h_case_j_eq_i : decide (digits[i]?.getD 0 % 2 = 1) = (digits[i]?.getD 0 == 1))
    : ∀ j < i, (result * 2 + digits[i]?.getD 0).testBit (i - j) = (digits[j]?.getD 0 == 1) := by
    intro j hj
    -- For j < i, we have i - j = (i - 1 - j) + 1
    have h_eq : i - j = (i - 1 - j) + 1 := by omega
    rw [h_eq]
    -- Apply h_testBit_add_small_succ
    rw [h_testBit_add_small_succ]
    -- Now we need result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1)
    exact invariant_bits_match j hj

theorem goal_0
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    : ∀ j < i + 1, (result * 2 + digits[i]?.getD 0).testBit (i - j) = (digits[j]?.getD 0 == 1) := by
    have h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1 := by (try simp at *; expose_names); exact (goal_0_0 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero); done
    have h_digit_lt_two : digits[i]?.getD 0 < 2 := by (try simp at *; expose_names); exact (goal_0_1 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid); done
    have h_mul_two_eq_shiftLeft : result * 2 = result <<< 1 := by (try simp at *; expose_names); exact (goal_0_2 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two); done
    have h_testBit_mul_two_zero : (result * 2).testBit 0 = false := by (try simp at *; expose_names); exact (goal_0_3 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two h_mul_two_eq_shiftLeft); done
    have h_testBit_mul_two_succ : ∀ k : ℕ, (result * 2).testBit (k + 1) = result.testBit k := by (try simp at *; expose_names); exact (goal_0_4 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two h_mul_two_eq_shiftLeft h_testBit_mul_two_zero); done
    have h_testBit_add_small_zero : (result * 2 + digits[i]?.getD 0).testBit 0 = (digits[i]?.getD 0 == 1) := by (try simp at *; expose_names); exact (goal_0_5 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two h_mul_two_eq_shiftLeft h_testBit_mul_two_succ h_testBit_mul_two_zero); done
    have h_testBit_add_small_succ : ∀ k : ℕ, (result * 2 + digits[i]?.getD 0).testBit (k + 1) = result.testBit k := by (try simp at *; expose_names); exact (goal_0_6 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two h_mul_two_eq_shiftLeft h_testBit_mul_two_succ h_testBit_mul_two_zero h_testBit_add_small_zero); done
    have h_case_j_eq_i : (result * 2 + digits[i]?.getD 0).testBit (i - i) = (digits[i]?.getD 0 == 1) := by (try simp at *; expose_names); exact (h_testBit_add_small_zero); done
    have h_case_j_lt_i : ∀ j < i, (result * 2 + digits[i]?.getD 0).testBit (i - j) = (digits[j]?.getD 0 == 1) := by (try simp at *; expose_names); exact (goal_0_7 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two h_mul_two_eq_shiftLeft h_testBit_mul_two_succ h_testBit_add_small_succ h_testBit_mul_two_zero h_testBit_add_small_zero h_case_j_eq_i); done
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | hj_eq
    · exact h_case_j_lt_i j hj_lt
    · rw [hj_eq]; exact h_case_j_eq_i

theorem goal_1_0
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    : result * 2 = result <<< 1 := by
    rw [Nat.shiftLeft_eq]

theorem goal_1_1
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    (h_mul_two_eq_shift : result * 2 = result <<< 1)
    : ∀ (k : ℕ), (result <<< 1).testBit (k + 1) = result.testBit k := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_2
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    (h_mul_two_eq_shift : result * 2 = result <<< 1)
    (h_testBit_shift_succ : True)
    (h_result_mul_two_lt : True)
    : ∀ (k : ℕ), (result * 2 + digits[i]?.getD 0).testBit (k + 1) = (result * 2).testBit (k + 1) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_3
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    (h_mul_two_eq_shift : result * 2 = result <<< 1)
    (h_testBit_add_succ : ∀ (k : ℕ), (result * 2 + digits[i]?.getD 0).testBit (k + 1) = (result * 2).testBit (k + 1))
    (h_testBit_shift_succ : True)
    (h_result_mul_two_lt : True)
    : ∀ (k : ℕ), (result * 2).testBit (k + 1) = result.testBit k := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_4
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    (h_mul_two_eq_shift : result * 2 = result <<< 1)
    (h_testBit_add_succ : ∀ (k : ℕ), (result * 2 + digits[i]?.getD 0).testBit (k + 1) = (result * 2).testBit (k + 1))
    (h_testBit_mul_two_succ : ∀ (k : ℕ), (result * 2).testBit (k + 1) = result.testBit k)
    (h_upper_bits_result : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (k : ℕ)
    (hk : i + 1 ≤ k)
    (h_k_pred : k = k - 1 + 1)
    (h_testBit_shift_succ : True)
    (h_result_mul_two_lt : True)
    (h_k_pos : 1 ≤ k)
    : (result * 2 + digits[i]?.getD 0).testBit k = (result * 2).testBit k := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_5
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1)
    (h_digit_lt_two : digits[i]?.getD 0 < 2)
    (h_mul_two_eq_shift : result * 2 = result <<< 1)
    (h_testBit_add_succ : ∀ (k : ℕ), (result * 2 + digits[i]?.getD 0).testBit (k + 1) = (result * 2).testBit (k + 1))
    (h_testBit_mul_two_succ : ∀ (k : ℕ), (result * 2).testBit (k + 1) = result.testBit k)
    (h_upper_bits_result : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (k : ℕ)
    (hk : i + 1 ≤ k)
    (h_k_pred : k = k - 1 + 1)
    (h_step1 : (result * 2 + digits[i]?.getD 0).testBit k = (result * 2).testBit k)
    (h_testBit_shift_succ : True)
    (h_result_mul_two_lt : True)
    (h_k_pos : 1 ≤ k)
    : (result * 2).testBit k = result.testBit (k - 1) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (if_pos : i < digits.length)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    : ∀ (k : ℕ), i + 1 ≤ k → (result * 2 + digits[i]?.getD 0).testBit k = false := by
    have h_digit_valid : digits[i]?.getD 0 = 0 ∨ digits[i]?.getD 0 = 1 := by (try simp at *; expose_names); exact (goal_0_0 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero); done
    have h_digit_lt_two : digits[i]?.getD 0 < 2 := by (try simp at *; expose_names); exact (goal_0_1 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid); done
    have h_mul_two_eq_shift : result * 2 = result <<< 1 := by (try simp at *; expose_names); exact (goal_1_0 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two); done
    have h_testBit_shift_succ : ∀ k : ℕ, (result <<< 1).testBit (k + 1) = result.testBit k := by (try simp at *; expose_names); exact (goal_1_1 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two h_mul_two_eq_shift); done
    have h_result_mul_two_lt : result * 2 % 2 = 0 := by (try simp at *; expose_names); exact (Nat.mul_mod_left result 2); done
    have h_testBit_add_succ : ∀ k : ℕ, (result * 2 + digits[i]?.getD 0).testBit (k + 1) = (result * 2).testBit (k + 1) := by (try simp at *; expose_names); exact (goal_1_2 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two h_mul_two_eq_shift h_testBit_shift_succ h_result_mul_two_lt); done
    have h_testBit_mul_two_succ : ∀ k : ℕ, (result * 2).testBit (k + 1) = result.testBit k := by (try simp at *; expose_names); exact (goal_1_3 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two h_mul_two_eq_shift h_testBit_add_succ h_testBit_shift_succ h_result_mul_two_lt); done
    have h_upper_bits_result : ∀ k : ℕ, i ≤ k → result.testBit k = false := by (try simp at *; expose_names); exact (fun k a ↦ invariant_upper_bits_zero k a); done
    intro k hk
    have h_k_pos : k ≥ 1 := by (try simp at *; expose_names); exact Nat.one_le_of_lt hk; done
    have h_k_pred : k = (k - 1) + 1 := by (try simp at *; expose_names); exact ((Nat.sub_eq_iff_eq_add h_k_pos).mp rfl); done
    have h_step1 : (result * 2 + digits[i]?.getD 0).testBit k = (result * 2).testBit k := by (try simp at *; expose_names); exact (goal_1_4 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two h_mul_two_eq_shift h_testBit_add_succ h_testBit_mul_two_succ h_upper_bits_result k hk h_k_pred h_testBit_shift_succ h_result_mul_two_lt h_k_pos); done
    have h_step2 : (result * 2).testBit k = result.testBit (k - 1) := by (try simp at *; expose_names); exact (goal_1_5 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero h_digit_valid h_digit_lt_two h_mul_two_eq_shift h_testBit_add_succ h_testBit_mul_two_succ h_upper_bits_result k hk h_k_pred h_step1 h_testBit_shift_succ h_result_mul_two_lt h_k_pos); done
    have h_k_minus_one_ge_i : i ≤ k - 1 := by (try simp at *; expose_names); exact ((Nat.le_sub_one_iff_lt h_k_pos).mpr hk); done
    have h_step3 : result.testBit (k - 1) = false := by (try simp at *; expose_names); exact (invariant_upper_bits_zero (k - 1) h_k_minus_one_ge_i); done
    rw [h_step1, h_step2, h_step3]

theorem goal_2
    (digits : List ℕ)
    (require_1 : precondition digits)
    (i : ℕ)
    (result : ℕ)
    (a_1 : i ≤ digits.length)
    (done_1 : i = digits.length)
    (i_1 : ℕ)
    (result_1 : ℕ)
    (a : True)
    (invariant_bits_match : ∀ j < i, result.testBit (i - 1 - j) = (digits[j]?.getD 0 == 1))
    (invariant_upper_bits_zero : ∀ (k : ℕ), i ≤ k → result.testBit k = false)
    (i_2 : i = i_1 ∧ result = result_1)
    : postcondition digits result_1 := by
    unfold postcondition
    obtain ⟨hi_eq, hr_eq⟩ := i_2
    subst hr_eq hi_eq done_1
    constructor
    · -- Part 1: digits.length = 0 → result = 0
      intro h_len_zero
      have h_all_bits_zero : ∀ k, result.testBit k = false := by
        intro k
        apply invariant_upper_bits_zero
        omega
      -- Show result = 0 using bit extensionality
      have h_eq : result = 0 := by
        apply Nat.eq_of_testBit_eq
        intro k
        rw [h_all_bits_zero k, Nat.zero_testBit]
      exact h_eq
    constructor
    · -- Part 2: ∀ i_idx, i_idx < digits.length → result.testBit (digits.length - 1 - i_idx) = (digits[i_idx]! == 1)
      intro j hj
      have h_inv := invariant_bits_match j hj
      -- Convert digits[j]?.getD 0 to digits[j]!
      have h_some : digits[j]? = some digits[j] := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨hj, rfl⟩
      have h_getD_eq : digits[j]?.getD 0 = digits[j] := by
        rw [h_some]
        rfl
      -- digits[j]! = (digits[j]?).getD default = (some digits[j]).getD 0 = digits[j]
      have h_bang_eq : digits[j]! = digits[j] := by
        rw [List.getElem!_eq_getElem?_getD, h_some]
        rfl
      rw [h_getD_eq] at h_inv
      rw [h_bang_eq]
      exact h_inv
    · -- Part 3: ∀ j, j ≥ digits.length → result.testBit j = false
      intro k hk
      apply invariant_upper_bits_zero
      exact hk


prove_correct binaryToDecimal by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero)
  exact (goal_1 digits require_1 i result a_1 if_pos a invariant_bits_match invariant_upper_bits_zero)
  exact (goal_2 digits require_1 i result a_1 done_1 i_1 result_1 a invariant_bits_match invariant_upper_bits_zero i_2)
end Proof
