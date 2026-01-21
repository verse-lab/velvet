import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isArmstrong: Determine whether a given number n is an Armstrong number
    Natural language breakdown:
    1. An Armstrong number (also called Narcissistic number) is a number that equals
       the sum of its own digits each raised to the power of the number of digits
    2. The number of digits k of n in base 10 is: if n = 0 then 1 else floor(log10(n)) + 1
    3. The digit at position i (0-indexed from right) is: (n / 10^i) % 10
    4. The Armstrong sum is: sum of (digit at position i)^k for i from 0 to k-1
    5. n is an Armstrong number iff the Armstrong sum equals n
    6. Examples:
       - 153 has 3 digits: 1^3 + 5^3 + 3^3 = 1 + 125 + 27 = 153 ✓
       - 9474 has 4 digits: 9^4 + 4^4 + 7^4 + 4^4 = 6561 + 256 + 2401 + 256 = 9474 ✓
       - 10 has 2 digits: 1^2 + 0^2 = 1 + 0 = 1 ≠ 10 ✗
    7. Edge cases:
       - 0 is an Armstrong number (0 has 1 digit, 0^1 = 0)
       - Single digit numbers (1-9) are all Armstrong numbers (d^1 = d)
-/

section Specs
register_specdef_allow_recursion

-- Number of digits in base 10 (mathematically defined)
def numDigits (n : Nat) : Nat :=
  if n < 10 then 1 else 1 + numDigits (n / 10)

-- Get digit at position i (0-indexed from right)
def digitAt (n : Nat) (i : Nat) : Nat :=
  (n / (10 ^ i)) % 10

-- Armstrong sum: sum of (digit at position i)^k for i from 0 to k-1
def armstrongSumAux (n : Nat) (k : Nat) (i : Nat) : Nat :=
  if i = 0 then 0
  else armstrongSumAux n k (i - 1) + (digitAt n (i - 1)) ^ k

def armstrongSum (n : Nat) : Nat :=
  let k := numDigits n
  armstrongSumAux n k k

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Bool) : Prop :=
  result = true ↔ armstrongSum n = n
end Specs

section Impl
method isArmstrong (n : Nat)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
    -- Step 1: Count the number of digits
    let mut k : Nat := 1
    let mut temp := n
    while temp >= 10
      -- k counts how many times we can divide temp by 10 plus 1
      -- temp >= 10 means we haven't finished counting
      invariant "k_positive" k ≥ 1
      invariant "temp_relation" temp > 0 → k + numDigits temp - 1 = numDigits n
      invariant "n_positive_case" n > 0 → temp > 0
      invariant "n_zero_case" n = 0 → temp = 0 ∧ k = 1
    do
      k := k + 1
      temp := temp / 10

    -- Step 2: Compute the Armstrong sum
    let mut sum : Nat := 0
    let mut remaining := n
    while remaining > 0
      -- sum accumulates the Armstrong sum of processed digits
      -- At termination, sum = armstrongSum n
      invariant "k_is_numDigits" k = numDigits n
      invariant "armstrong_partial" sum + armstrongSumAux remaining k (numDigits remaining) = armstrongSum n
    do
      let digit := remaining % 10
      sum := sum + digit ^ k
      remaining := remaining / 10

    -- Special case: n = 0 has Armstrong sum 0 (0^1 = 0)
    -- The loop doesn't execute when n = 0, so sum stays 0, which equals n

    -- Step 3: Check if sum equals n
    return (sum == n)
end Impl

section TestCases
-- Test case 1: 0 is an Armstrong number (0^1 = 0)
def test1_n : Nat := 0
def test1_Expected : Bool := true

-- Test case 2: 1 is an Armstrong number (1^1 = 1)
def test2_n : Nat := 1
def test2_Expected : Bool := true

-- Test case 3: 10 is not an Armstrong number (1^2 + 0^2 = 1 ≠ 10)
def test3_n : Nat := 10
def test3_Expected : Bool := false

-- Test case 4: 153 is an Armstrong number (1^3 + 5^3 + 3^3 = 153)
def test4_n : Nat := 153
def test4_Expected : Bool := true

-- Test case 5: 9474 is an Armstrong number (9^4 + 4^4 + 7^4 + 4^4 = 9474)
def test5_n : Nat := 9474
def test5_Expected : Bool := true

-- Test case 6: 9475 is not an Armstrong number
def test6_n : Nat := 9475
def test6_Expected : Bool := false

-- Test case 7: 370 is an Armstrong number (3^3 + 7^3 + 0^3 = 27 + 343 + 0 = 370)
def test7_n : Nat := 370
def test7_Expected : Bool := true

-- Test case 8: 9 is an Armstrong number (single digit, 9^1 = 9)
def test8_n : Nat := 9
def test8_Expected : Bool := true

-- Test case 9: 100 is not an Armstrong number (1^3 + 0^3 + 0^3 = 1 ≠ 100)
def test9_n : Nat := 100
def test9_Expected : Bool := false

-- Recommend to validate: 3, 4, 5 (covers false case 10, classic 3-digit Armstrong 153, and 4-digit 9474)
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((isArmstrong test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isArmstrong test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isArmstrong test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isArmstrong test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isArmstrong test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isArmstrong test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isArmstrong test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isArmstrong test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isArmstrong test9_n).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for isArmstrong
prove_precondition_decidable_for isArmstrong
prove_postcondition_decidable_for isArmstrong
derive_tester_for isArmstrong
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
    let res := isArmstrongTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break

end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isArmstrong by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (if_pos : 10 ≤ temp)
    : 10 ≤ temp → k + numDigits (temp / 10) = numDigits n := by
    intro h_ge_10
    have h_temp_pos : 0 < temp := Nat.lt_of_lt_of_le (by omega : 0 < 10) h_ge_10
    have h_inv := invariant_temp_relation h_temp_pos
    -- When temp ≥ 10, numDigits temp = 1 + numDigits (temp / 10)
    have h_not_lt_10 : ¬(temp < 10) := Nat.not_lt.mpr h_ge_10
    have h_numDigits_temp : numDigits temp = 1 + numDigits (temp / 10) := by
      conv_lhs => unfold numDigits
      simp only [h_not_lt_10, ↓reduceIte]
    -- From h_inv: k + numDigits temp - 1 = numDigits n
    -- Substitute: k + (1 + numDigits (temp / 10)) - 1 = numDigits n
    -- Simplify: k + numDigits (temp / 10) = numDigits n
    calc k + numDigits (temp / 10)
        = k + (1 + numDigits (temp / 10)) - 1 := by omega
      _ = k + numDigits temp - 1 := by rw [h_numDigits_temp]
      _ = numDigits n := h_inv

theorem goal_1_0
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    : 1 ≤ numDigits remaining := by
    unfold numDigits
    split
    · -- Case: remaining < 10, so numDigits remaining = 1
      exact Nat.le_refl 1
    · -- Case: remaining ≥ 10, so numDigits remaining = 1 + numDigits (remaining / 10)
      exact Nat.le_add_right 1 _

theorem goal_1_1
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    : digitAt remaining 0 = remaining % 10 := by
    unfold digitAt
    simp [Nat.pow_zero, Nat.div_one]

theorem goal_1_2
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i := by
    conv_lhs => unfold armstrongSumAux
    simp only [if_neg h_numDigits_remaining_ne_zero]

theorem goal_1_3_0
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    : remaining < 10 → numDigits remaining = 1 := by
    intro h_lt
    unfold numDigits
    simp [h_lt]

theorem goal_1_3_1
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_case_lt_10 : remaining < 10 → numDigits remaining = 1)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    : 10 ≤ remaining → numDigits remaining = 1 + numDigits (remaining / 10) := by
    intro h
    have h_not_lt : ¬(remaining < 10) := Nat.not_lt.mpr h
    conv_lhs => unfold numDigits
    simp only [h_not_lt, ↓reduceIte]

theorem goal_1_3
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1 := by
    have h_cases : remaining < 10 ∨ ¬(remaining < 10) := by (try simp at *; expose_names); exact (Nat.lt_or_ge remaining 10); done
    have h_case_lt_10 : remaining < 10 → numDigits remaining = 1 := by (try simp at *; expose_names); exact (goal_1_3_0 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases); done
    have h_case_ge_10 : ¬(remaining < 10) → numDigits remaining = 1 + numDigits (remaining / 10) := by (try simp at *; expose_names); exact (goal_1_3_1 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_case_lt_10 h_cases); done
    cases h_cases with
    | inl h_lt =>
      have h_numDigits_eq_1 : numDigits remaining = 1 := h_case_lt_10 h_lt
      exact Or.inr ⟨h_lt, h_numDigits_eq_1⟩
    | inr h_ge =>
      have h_numDigits_recursive : numDigits remaining = 1 + numDigits (remaining / 10) := h_case_ge_10 h_ge
      exact Or.inl h_numDigits_recursive

theorem goal_1_4_0
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_case_lt_10 : True)
    : numDigits 0 = 1 := by
    unfold numDigits
    simp

theorem goal_1_4_1
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_case_lt_10 : True)
    : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k := by
  intro m k'
  unfold armstrongSumAux
  simp only [Nat.one_ne_zero, ↓reduceIte, Nat.sub_self]
  unfold armstrongSumAux
  simp only [↓reduceIte, Nat.zero_add]

theorem goal_1_4_2
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_case_lt_10 : True)
    : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0 := by
    intro m k'
    unfold armstrongSumAux
    simp

theorem goal_1_4_3
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_case_lt_10 : True)
    : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j := by
  intro m j
  unfold digitAt
  -- Need to show: (m / 10 ^ (j + 1)) % 10 = (m / 10 / 10 ^ j) % 10
  -- Using: 10 ^ (j + 1) = 10 * 10 ^ j and m / (a * b) = m / a / b
  have h1 : 10 ^ (j + 1) = 10 * 10 ^ j := by
    rw [Nat.pow_succ']
  rw [h1]
  -- Now need: (m / (10 * 10 ^ j)) % 10 = (m / 10 / 10 ^ j) % 10
  -- Nat.div_div_eq_div_mul says: m / n / k = m / (n * k)
  -- So m / 10 / 10^j = m / (10 * 10^j)
  -- We need the symmetric version
  have h2 : m / (10 * 10 ^ j) = m / 10 / 10 ^ j := by
    have := Nat.div_div_eq_div_mul m 10 (10 ^ j)
    omega
  rw [h2]

theorem goal_1_4_4_0
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_case_lt_10 : True)
    (m' : ℕ)
    (k' : ℕ)
    (j : ℕ)
    (h_j_le : j ≤ numDigits (m' / 10))
    (h_j_pos : 0 < j)
    (h_j_ne_zero : ¬j = 0)
    (j' : ℕ)
    (h_j_eq : j = j' + 1)
    : armstrongSumAux m' k' j = armstrongSumAux m' k' (j - 1) + digitAt m' (j - 1) ^ k' := by
    sorry

theorem goal_1_4_4_1
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_case_lt_10 : True)
    (m' : ℕ)
    (k' : ℕ)
    (j : ℕ)
    (h_j_le : j ≤ numDigits (m' / 10))
    (h_j_pos : 0 < j)
    (h_j_ne_zero : ¬j = 0)
    (j' : ℕ)
    (h_j_eq : j = j' + 1)
    (h_armstrongSumAux_unfold_j : armstrongSumAux m' k' j = armstrongSumAux m' k' (j - 1) + digitAt m' (j - 1) ^ k')
    (h_j_minus_one : j - 1 = j')
    : digitAt m' j' = digitAt (m' / 10) j' := by
    sorry

theorem goal_1_4_4_2
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_case_lt_10 : True)
    (m' : ℕ)
    (k' : ℕ)
    (j : ℕ)
    (h_j_le : j ≤ numDigits (m' / 10))
    (h_j_pos : 0 < j)
    (h_j_ne_zero : ¬j = 0)
    (j' : ℕ)
    (h_j_eq : j = j' + 1)
    (h_armstrongSumAux_unfold_j : armstrongSumAux m' k' j = armstrongSumAux m' k' (j - 1) + digitAt m' (j - 1) ^ k')
    (h_j_minus_one : j - 1 = j')
    (h_digitAt_shift_applied : digitAt m' j' = digitAt (m' / 10) j')
    : armstrongSumAux m' k' j = digitAt m' 0 ^ k' + armstrongSumAux (m' / 10) k' (j - 1) := by
    sorry

theorem goal_1_4_4
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_case_lt_10 : True)
    : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0 := by
  intro m' k' j h_j_le
  have h_j_cases : j = 0 ∨ 0 < j := by (try simp at *; expose_names); exact (Nat.eq_zero_or_pos j); done
  cases h_j_cases with
  | inl h_j_zero =>
    have h_right_disjunct : j = 0 := by (try simp at *; expose_names); exact h_j_zero; done
    exact Or.inr h_right_disjunct
  | inr h_j_pos =>
    have h_j_ne_zero : j ≠ 0 := by (try simp at *; expose_names); exact (Nat.ne_zero_of_lt h_j_pos); done
    have h_j_eq_succ : ∃ j', j = j' + 1 := by (try simp at *; expose_names); exact h_j_pos; done
    obtain ⟨j', h_j_eq⟩ := h_j_eq_succ
    have h_armstrongSumAux_unfold_j : armstrongSumAux m' k' j = armstrongSumAux m' k' (j - 1) + digitAt m' (j - 1) ^ k' := by (try simp at *; expose_names); exact (goal_1_4_4_0 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_numDigits_relation h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_case_lt_10 m' k' j h_j_le h_j_pos h_j_ne_zero j' h_j_eq); done
    have h_j_minus_one : j - 1 = j' := by (try simp at *; expose_names); exact (Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm h_j_eq)))); done
    have h_digitAt_shift_applied : digitAt m' j' = digitAt (m' / 10) j' := by (try simp at *; expose_names); exact (goal_1_4_4_1 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_numDigits_relation h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_case_lt_10 m' k' j h_j_le h_j_pos h_j_ne_zero j' h_j_eq h_armstrongSumAux_unfold_j h_j_minus_one); done
    have h_equation_holds : armstrongSumAux m' k' j = digitAt m' 0 ^ k' + armstrongSumAux (m' / 10) k' (j - 1) := by (try simp at *; expose_names); exact (goal_1_4_4_2 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_numDigits_relation h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_case_lt_10 m' k' j h_j_le h_j_pos h_j_ne_zero j' h_j_eq h_armstrongSumAux_unfold_j h_j_minus_one h_digitAt_shift_applied); done
    exact Or.inl h_equation_holds

theorem goal_1_4_5
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_case_lt_10 : True)
    : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0 := by
    let d := numDigits (remaining / 10)
    by_cases hd : d = 0
    · right
      exact hd
    · left
      have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      have h1 : numDigits remaining - 1 = d := h_numDigits_sub
      rw [h1]
      have h2 : (d - 1) + 1 = d := Nat.sub_one_add_one hd
      have h3 : digitAt remaining ((d - 1) + 1) = digitAt (remaining / 10) (d - 1) := h_digitAt_shift remaining (d - 1)
      rw [h2] at h3
      exact h3

theorem goal_1_4_6_0
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_case_lt_10 : True)
    : 1 ≤ numDigits (remaining / 10) := by
    sorry

theorem goal_1_4_6_1
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_case_lt_10 : True)
    (h_numDigits_div_ge_1 : 1 ≤ numDigits (remaining / 10))
    (h_numDigits_div_ne_zero : ¬numDigits (remaining / 10) = 0)
    (h_j_le_refl : True)
    : armstrongSumAux remaining i (numDigits (remaining / 10)) = digitAt remaining 0 ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0 := by
    sorry

theorem goal_1_4_6_2
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_case_lt_10 : True)
    (h_numDigits_div_ge_1 : 1 ≤ numDigits (remaining / 10))
    (h_numDigits_div_ne_zero : ¬numDigits (remaining / 10) = 0)
    (h_shift_applied : armstrongSumAux remaining i (numDigits (remaining / 10)) = digitAt remaining 0 ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_digitAt_eq_mod : digitAt remaining 0 ^ i = (remaining % 10) ^ i)
    (h_numDigits_sub_add : numDigits (remaining / 10) - 1 + 1 = numDigits (remaining / 10))
    (h_j_le_refl : True)
    : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) + digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i := by
    sorry

theorem goal_1_4_6_3
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_case_lt_10 : True)
    (h_numDigits_div_ge_1 : 1 ≤ numDigits (remaining / 10))
    (h_numDigits_div_ne_zero : ¬numDigits (remaining / 10) = 0)
    (h_shift_applied : armstrongSumAux remaining i (numDigits (remaining / 10)) = digitAt remaining 0 ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_digitAt_eq_mod : digitAt remaining 0 ^ i = (remaining % 10) ^ i)
    (h_numDigits_sub_add : numDigits (remaining / 10) - 1 + 1 = numDigits (remaining / 10))
    (h_aux_unfold_div : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) + digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i)
    (h_j_le_refl : True)
    : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) := by
    sorry

theorem goal_1_4_6_4
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_case_lt_10 : True)
    (h_numDigits_div_ge_1 : 1 ≤ numDigits (remaining / 10))
    (h_numDigits_div_ne_zero : ¬numDigits (remaining / 10) = 0)
    (h_shift_applied : armstrongSumAux remaining i (numDigits (remaining / 10)) = digitAt remaining 0 ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_digitAt_eq_mod : digitAt remaining 0 ^ i = (remaining % 10) ^ i)
    (h_numDigits_sub_add : numDigits (remaining / 10) - 1 + 1 = numDigits (remaining / 10))
    (h_aux_unfold_div : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) + digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i)
    (h_main_case : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1))
    (h_substitute : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) - digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i)
    (h_add_sub_cancel : ∀ (a b c : ℕ), c ≤ b → a + (b - c) = a + b - c)
    (h_j_le_refl : True)
    (h_final_eq : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) - digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i)
    : digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i ≤ armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by
    sorry

theorem goal_1_4_6_5
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_case_lt_10 : True)
    (h_numDigits_div_ge_1 : 1 ≤ numDigits (remaining / 10))
    (h_numDigits_div_ne_zero : ¬numDigits (remaining / 10) = 0)
    (h_shift_applied : armstrongSumAux remaining i (numDigits (remaining / 10)) = digitAt remaining 0 ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_digitAt_eq_mod : digitAt remaining 0 ^ i = (remaining % 10) ^ i)
    (h_numDigits_sub_add : numDigits (remaining / 10) - 1 + 1 = numDigits (remaining / 10))
    (h_aux_unfold_div : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) + digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i)
    (h_main_case : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1))
    (h_substitute : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) - digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i)
    (h_add_sub_cancel : ∀ (a b c : ℕ), c ≤ b → a + (b - c) = a + b - c)
    (h_digit_le_aux : digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i ≤ armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))
    (h_j_le_refl : True)
    (h_final_eq : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) - digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i)
    : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by
    sorry

theorem goal_1_4_6
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_case_lt_10 : True)
    : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by
    have h_numDigits_div_ge_1 : 1 ≤ numDigits (remaining / 10) := by (try simp at *; expose_names); exact (goal_1_4_6_0 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_case_lt_10); done
    have h_numDigits_div_ne_zero : ¬numDigits (remaining / 10) = 0 := by (try simp at *; expose_names); exact (Nat.ne_zero_of_lt h_numDigits_div_ge_1); done
    have h_j_le_refl : numDigits (remaining / 10) ≤ numDigits (remaining / 10) := by (try simp at *; expose_names); exact (Nat.le_refl (numDigits (remaining / 10))); done
    have h_shift_applied : armstrongSumAux remaining i (numDigits (remaining / 10)) = digitAt remaining 0 ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0 := by (try simp at *; expose_names); exact (goal_1_4_6_1 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_case_lt_10 h_numDigits_div_ge_1 h_numDigits_div_ne_zero h_j_le_refl); done
    have h_digitAt_eq_mod : digitAt remaining 0 ^ i = (remaining % 10) ^ i := by (try simp at *; expose_names); exact (congrFun (congrArg HPow.hPow h_digitAt_zero) i); done
    have h_numDigits_sub_add : numDigits (remaining / 10) - 1 + 1 = numDigits (remaining / 10) := by (try simp at *; expose_names); exact (Nat.sub_add_cancel h_numDigits_div_ge_1); done
    have h_aux_unfold_div : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) + digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i := by (try simp at *; expose_names); exact (goal_1_4_6_2 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_case_lt_10 h_numDigits_div_ge_1 h_numDigits_div_ne_zero h_shift_applied h_digitAt_eq_mod h_numDigits_sub_add h_j_le_refl); done
    have h_main_case : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) := by (try simp at *; expose_names); exact (goal_1_4_6_3 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_case_lt_10 h_numDigits_div_ge_1 h_numDigits_div_ne_zero h_shift_applied h_digitAt_eq_mod h_numDigits_sub_add h_aux_unfold_div h_j_le_refl); done
    have h_substitute : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) - digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i := by (try simp at *; expose_names); exact (Nat.eq_sub_of_add_eq (id (Eq.symm h_aux_unfold_div))); done
    have h_final_eq : (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) = (remaining % 10) ^ i + (armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) - digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i) := by (try simp at *; expose_names); exact (h_substitute); done
    have h_add_sub_cancel : ∀ a b c : ℕ, c ≤ b → a + (b - c) = a + b - c := by (try simp at *; expose_names); exact (fun a b c a_1 ↦ Eq.symm (Nat.add_sub_assoc a_1 a)); done
    have h_digit_le_aux : digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i ≤ armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by (try simp at *; expose_names); exact (goal_1_4_6_4 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_case_lt_10 h_numDigits_div_ge_1 h_numDigits_div_ne_zero h_shift_applied h_digitAt_eq_mod h_numDigits_sub_add h_aux_unfold_div h_main_case h_substitute h_add_sub_cancel h_j_le_refl h_final_eq); done
    calc armstrongSumAux remaining i (numDigits (remaining / 10))
        = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) := h_main_case
      _ = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by (try simp at *; expose_names); exact (goal_1_4_6_5 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_case_lt_10 h_numDigits_div_ge_1 h_numDigits_div_ne_zero h_shift_applied h_digitAt_eq_mod h_numDigits_sub_add h_aux_unfold_div h_main_case h_substitute h_add_sub_cancel h_digit_le_aux h_j_le_refl h_final_eq); done

theorem goal_1_4_7_0
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_armstrongSumAux_eq : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))
    (h_case_lt_10 : True)
    (h_sub_eq_div : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_rewrite_sub : armstrongSumAux remaining i (numDigits remaining - 1) = armstrongSumAux remaining i (numDigits (remaining / 10)))
    : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i := by
    sorry

theorem goal_1_4_7_1
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_armstrongSumAux_eq : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))
    (h_case_lt_10 : True)
    (h_sub_eq_div : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_rewrite_sub : armstrongSumAux remaining i (numDigits remaining - 1) = armstrongSumAux remaining i (numDigits (remaining / 10)))
    (h_lhs_step1 : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i)
    (h_digitAt_last_pos : numDigits (remaining / 10) = numDigits remaining - 1)
    : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0 := by
    sorry

theorem goal_1_4_7_2
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_armstrongSumAux_eq : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))
    (h_case_lt_10 : True)
    (h_sub_eq_div : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_rewrite_sub : armstrongSumAux remaining i (numDigits remaining - 1) = armstrongSumAux remaining i (numDigits (remaining / 10)))
    (h_lhs_step1 : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i)
    (h_digitAt_last_pos : numDigits (remaining / 10) = numDigits remaining - 1)
    (h_digitAt_shift_applied : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i := by
    sorry

theorem goal_1_4_7_3
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_armstrongSumAux_eq : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))
    (h_case_lt_10 : True)
    (h_sub_eq_div : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_rewrite_sub : armstrongSumAux remaining i (numDigits remaining - 1) = armstrongSumAux remaining i (numDigits (remaining / 10)))
    (h_lhs_step1 : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i)
    (h_digitAt_last_pos : numDigits (remaining / 10) = numDigits remaining - 1)
    (h_digitAt_shift_applied : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_expand_lhs : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i)
    : 1 ≤ numDigits (remaining / 10) := by
    sorry

theorem goal_1_4_7_4
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_armstrongSumAux_eq : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))
    (h_case_lt_10 : True)
    (h_sub_eq_div : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_rewrite_sub : armstrongSumAux remaining i (numDigits remaining - 1) = armstrongSumAux remaining i (numDigits (remaining / 10)))
    (h_lhs_step1 : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i)
    (h_digitAt_last_pos : numDigits (remaining / 10) = numDigits remaining - 1)
    (h_digitAt_shift_applied : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_expand_lhs : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i)
    (h_numDigits_div_pos : 1 ≤ numDigits (remaining / 10))
    (h_numDigits_div_ne_zero : ¬numDigits (remaining / 10) = 0)
    : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) := by
    sorry

theorem goal_1_4_7_5
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_armstrongSumAux_eq : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))
    (h_case_lt_10 : True)
    (h_sub_eq_div : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_rewrite_sub : armstrongSumAux remaining i (numDigits remaining - 1) = armstrongSumAux remaining i (numDigits (remaining / 10)))
    (h_lhs_step1 : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i)
    (h_digitAt_last_pos : numDigits (remaining / 10) = numDigits remaining - 1)
    (h_digitAt_shift_applied : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_expand_lhs : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i)
    (h_numDigits_div_pos : 1 ≤ numDigits (remaining / 10))
    (h_numDigits_div_ne_zero : ¬numDigits (remaining / 10) = 0)
    (h_digitAt_eq : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1))
    : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) + digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i := by
    sorry

theorem goal_1_4_7_6
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_armstrongSumAux_eq : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))
    (h_case_lt_10 : True)
    (h_sub_eq_div : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_rewrite_sub : armstrongSumAux remaining i (numDigits remaining - 1) = armstrongSumAux remaining i (numDigits (remaining / 10)))
    (h_lhs_step1 : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i)
    (h_digitAt_last_pos : numDigits (remaining / 10) = numDigits remaining - 1)
    (h_digitAt_shift_applied : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_expand_lhs : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i)
    (h_numDigits_div_pos : 1 ≤ numDigits (remaining / 10))
    (h_numDigits_div_ne_zero : ¬numDigits (remaining / 10) = 0)
    (h_digitAt_eq : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1))
    (h_armstrongSumAux_div_unfold : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) + digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i)
    : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by
    sorry

theorem goal_1_4_7
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_ge_10_case : numDigits remaining = 1 + numDigits (remaining / 10))
    (h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10))
    (h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0)
    (h_armstrongSumAux_eq : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))
    (h_case_lt_10 : True)
    : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by
  have h_sub_eq_div : numDigits remaining - 1 = numDigits (remaining / 10) := by (try simp at *; expose_names); exact (h_numDigits_sub); done
  have h_rewrite_sub : armstrongSumAux remaining i (numDigits remaining - 1) = armstrongSumAux remaining i (numDigits (remaining / 10)) := by (try simp at *; expose_names); exact (congrArg (armstrongSumAux remaining i) h_numDigits_sub); done
  have h_lhs_step1 : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i := by (try simp at *; expose_names); exact (goal_1_4_7_0 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_armstrongSumAux_eq h_case_lt_10 h_sub_eq_div h_rewrite_sub); done
  have h_digitAt_last_pos : numDigits (remaining / 10) = (numDigits remaining - 1) := by (try simp at *; expose_names); exact (id (Eq.symm h_numDigits_sub)); done
  have h_digitAt_shift_applied : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0 := by (try simp at *; expose_names); exact (goal_1_4_7_1 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_armstrongSumAux_eq h_case_lt_10 h_sub_eq_div h_rewrite_sub h_lhs_step1 h_digitAt_last_pos); done
  have h_expand_lhs : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i := by (try simp at *; expose_names); exact (goal_1_4_7_2 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_armstrongSumAux_eq h_case_lt_10 h_sub_eq_div h_rewrite_sub h_lhs_step1 h_digitAt_last_pos h_digitAt_shift_applied); done
  have h_numDigits_div_pos : 1 ≤ numDigits (remaining / 10) := by (try simp at *; expose_names); exact (goal_1_4_7_3 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_armstrongSumAux_eq h_case_lt_10 h_sub_eq_div h_rewrite_sub h_lhs_step1 h_digitAt_last_pos h_digitAt_shift_applied h_expand_lhs); done
  have h_numDigits_div_ne_zero : numDigits (remaining / 10) ≠ 0 := by (try simp at *; expose_names); exact (Nat.ne_zero_of_lt h_numDigits_div_pos); done
  have h_digitAt_eq : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) := by (try simp at *; expose_names); exact (goal_1_4_7_4 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_armstrongSumAux_eq h_case_lt_10 h_sub_eq_div h_rewrite_sub h_lhs_step1 h_digitAt_last_pos h_digitAt_shift_applied h_expand_lhs h_numDigits_div_pos h_numDigits_div_ne_zero); done
  have h_armstrongSumAux_div_unfold : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) + digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i := by (try simp at *; expose_names); exact (goal_1_4_7_5 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_armstrongSumAux_eq h_case_lt_10 h_sub_eq_div h_rewrite_sub h_lhs_step1 h_digitAt_last_pos h_digitAt_shift_applied h_expand_lhs h_numDigits_div_pos h_numDigits_div_ne_zero h_digitAt_eq); done
  have h_final_eq : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by (try simp at *; expose_names); exact (goal_1_4_7_6 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_armstrongSumAux_eq h_case_lt_10 h_sub_eq_div h_rewrite_sub h_lhs_step1 h_digitAt_last_pos h_digitAt_shift_applied h_expand_lhs h_numDigits_div_pos h_numDigits_div_ne_zero h_digitAt_eq h_armstrongSumAux_div_unfold); done
  exact h_final_eq

theorem goal_1_4_8
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_lt_10_case : remaining < 10 ∧ numDigits remaining = 1)
    (h_lt : remaining < 10)
    (h_numDigits_eq_1 : numDigits remaining = 1)
    (h_case_lt_10 : True)
    (h_div_zero : remaining < 10)
    : numDigits (remaining / 10) = 1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_4_9
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_lt_10_case : remaining < 10 ∧ numDigits remaining = 1)
    (h_lt : remaining < 10)
    (h_numDigits_eq_1 : numDigits remaining = 1)
    (h_numDigits_div : numDigits (remaining / 10) = 1)
    (h_case_lt_10 : True)
    (h_div_zero : remaining < 10)
    : armstrongSumAux 0 i 1 = 0 := by
  have h_i_pos : 0 < i := by
    rw [invariant_k_is_numDigits]
    unfold numDigits
    split_ifs <;> omega
  rw [h_armstrongSumAux_one]
  unfold digitAt
  simp only [Nat.pow_zero, Nat.div_one, Nat.zero_mod]
  exact Nat.zero_pow h_i_pos

theorem goal_1_4_10
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_lt_10_case : remaining < 10 ∧ numDigits remaining = 1)
    (h_lt : remaining < 10)
    (h_numDigits_eq_1 : numDigits remaining = 1)
    (h_numDigits_div : numDigits (remaining / 10) = 1)
    (h_armstrongSumAux_div : armstrongSumAux 0 i 1 = 0)
    (h_case_lt_10 : True)
    (h_div_zero : remaining < 10)
    : armstrongSumAux remaining i 1 = (remaining % 10) ^ i := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_4_11
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_cases : remaining < 10 ∨ 10 ≤ remaining)
    (h_numDigits_zero : numDigits 0 = 1)
    (h_armstrongSumAux_one : ∀ (m k : ℕ), armstrongSumAux m k 1 = digitAt m 0 ^ k)
    (h_armstrongSumAux_zero : ∀ (m k : ℕ), armstrongSumAux m k 0 = 0)
    (h_digitAt_shift : ∀ (m j : ℕ), digitAt m (j + 1) = digitAt (m / 10) j)
    (h_armstrongSumAux_shift : ∀ (m k j : ℕ), j ≤ numDigits (m / 10) → armstrongSumAux m k j = digitAt m 0 ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0)
    (h_lt_10_case : remaining < 10 ∧ numDigits remaining = 1)
    (h_lt : remaining < 10)
    (h_numDigits_eq_1 : numDigits remaining = 1)
    (h_numDigits_div : numDigits (remaining / 10) = 1)
    (h_armstrongSumAux_div : armstrongSumAux 0 i 1 = 0)
    (h_lhs : armstrongSumAux remaining i 1 = (remaining % 10) ^ i)
    (h_case_lt_10 : True)
    (h_div_zero : remaining < 10)
    (h_remaining_mod : remaining < 10)
    : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_4
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1)
    : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by
    have h_cases : remaining < 10 ∨ 10 ≤ remaining := by (try simp at *; expose_names); exact (Nat.lt_or_ge remaining 10); done
    have h_case_lt_10 : remaining < 10 → remaining / 10 = 0 := by (try simp at *; expose_names); exact (fun a ↦ Nat.div_eq_of_lt a); done
    have h_numDigits_zero : numDigits 0 = 1 := by (try simp at *; expose_names); exact (goal_1_4_0 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_numDigits_relation h_cases h_case_lt_10); done
    have h_armstrongSumAux_one : ∀ m k, armstrongSumAux m k 1 = (digitAt m 0) ^ k := by (try simp at *; expose_names); exact (goal_1_4_1 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_numDigits_relation h_cases h_numDigits_zero h_case_lt_10); done
    have h_armstrongSumAux_zero : ∀ m k, armstrongSumAux m k 0 = 0 := by (try simp at *; expose_names); exact (goal_1_4_2 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_numDigits_relation h_cases h_numDigits_zero h_armstrongSumAux_one h_case_lt_10); done
    have h_digitAt_shift : ∀ m j, digitAt m (j + 1) = digitAt (m / 10) j := by (try simp at *; expose_names); exact (goal_1_4_3 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_numDigits_relation h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_case_lt_10); done
    have h_armstrongSumAux_shift : ∀ m k j, j ≤ numDigits (m / 10) → armstrongSumAux m k j = (digitAt m 0) ^ k + armstrongSumAux (m / 10) k (j - 1) ∨ j = 0 := by (try simp at *; expose_names); exact (goal_1_4_4 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_numDigits_relation h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_case_lt_10); done
    cases h_numDigits_relation with
    | inl h_ge_10_case =>
      have h_numDigits_sub : numDigits remaining - 1 = numDigits (remaining / 10) := by (try simp at *; expose_names); exact (Eq.symm (Nat.eq_sub_of_add_eq' (id (Eq.symm h_ge_10_case)))); done
      have h_digitAt_last : digitAt remaining (numDigits remaining - 1) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0 := by (try simp at *; expose_names); exact (goal_1_4_5 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_case_lt_10); done
      have h_armstrongSumAux_eq : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by (try simp at *; expose_names); exact (goal_1_4_6 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_case_lt_10); done
      (try simp at *; expose_names); exact (goal_1_4_7 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_armstrongSumAux_eq h_case_lt_10); done
    | inr h_lt_10_case =>
      have h_lt : remaining < 10 := h_lt_10_case.1
      have h_numDigits_eq_1 : numDigits remaining = 1 := h_lt_10_case.2
      have h_div_zero : remaining / 10 = 0 := by (try simp at *; expose_names); exact h_lt; done
      have h_numDigits_div : numDigits (remaining / 10) = 1 := by (try simp at *; expose_names); exact (goal_1_4_8 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_lt_10_case h_lt h_numDigits_eq_1 h_case_lt_10 h_div_zero); done
      have h_armstrongSumAux_div : armstrongSumAux 0 i 1 = 0 := by (try simp at *; expose_names); exact (goal_1_4_9 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_lt_10_case h_lt h_numDigits_eq_1 h_numDigits_div h_case_lt_10 h_div_zero); done
      have h_lhs : armstrongSumAux remaining i 1 = (remaining % 10) ^ i := by (try simp at *; expose_names); exact (goal_1_4_10 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_lt_10_case h_lt h_numDigits_eq_1 h_numDigits_div h_armstrongSumAux_div h_case_lt_10 h_div_zero); done
      have h_remaining_mod : remaining % 10 = remaining := by (try simp at *; expose_names); exact (h_lt); done
      (try simp at *; expose_names); exact (goal_1_4_11 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_lt_10_case h_lt h_numDigits_eq_1 h_numDigits_div h_armstrongSumAux_div h_lhs h_case_lt_10 h_div_zero h_remaining_mod); done

theorem goal_1_5
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    (h_remaining_pos : 0 < remaining)
    (h_numDigits_remaining_pos : 1 ≤ numDigits remaining)
    (h_numDigits_remaining_ne_zero : ¬numDigits remaining = 0)
    (h_digitAt_zero : digitAt remaining 0 = remaining % 10)
    (h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + digitAt remaining (numDigits remaining - 1) ^ i)
    (h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ remaining < 10 ∧ numDigits remaining = 1)
    (h_decomposition : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))
    : sum + armstrongSumAux remaining i (numDigits remaining) = sum + (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (if_pos : 0 < remaining)
    : sum + (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSum n := by
    have h_remaining_pos : 0 < remaining := if_pos
    have h_numDigits_remaining_pos : 1 ≤ numDigits remaining := by (try simp at *; expose_names); exact (goal_1_0 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos); done
    have h_numDigits_remaining_ne_zero : numDigits remaining ≠ 0 := by (try simp at *; expose_names); exact (Nat.ne_zero_of_lt h_numDigits_remaining_pos); done
    have h_digitAt_zero : digitAt remaining 0 = remaining % 10 := by (try simp at *; expose_names); exact (goal_1_1 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero); done
    have h_armstrongSumAux_unfold : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits remaining - 1) + (digitAt remaining (numDigits remaining - 1)) ^ i := by (try simp at *; expose_names); exact (goal_1_2 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero); done
    have h_numDigits_relation : numDigits remaining = 1 + numDigits (remaining / 10) ∨ (remaining < 10 ∧ numDigits remaining = 1) := by (try simp at *; expose_names); exact (goal_1_3 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold); done
    have h_decomposition : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by (try simp at *; expose_names); exact (goal_1_4 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_numDigits_relation); done
    have h_rewrite_invariant : sum + armstrongSumAux remaining i (numDigits remaining) = sum + (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) := by (try simp at *; expose_names); exact (goal_1_5 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_numDigits_relation h_decomposition); done
    have h_add_assoc : sum + (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = sum + ((remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10))) := by (try simp at *; expose_names); exact (Nat.add_assoc sum ((remaining % 10) ^ i) (armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)))); done
    calc sum + (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10))
        = sum + ((remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10))) := by rw [Nat.add_assoc]
      _ = sum + armstrongSumAux remaining i (numDigits remaining) := by rw [← h_decomposition]
      _ = armstrongSum n := invariant_armstrong_partial

theorem goal_2
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    : i = numDigits n := by
    have hki : k = i := i_1.1
    rw [← hki]
    cases Nat.eq_zero_or_pos n with
    | inl h_n_zero =>
      -- Case n = 0
      have h := invariant_n_zero_case h_n_zero
      have hk1 : k = 1 := h.2
      have h_numDigits_0 : numDigits 0 = 1 := by
        unfold numDigits
        simp
      rw [hk1, h_n_zero, h_numDigits_0]
    | inr h_n_pos =>
      -- Case n > 0
      have h_temp_pos : 0 < temp := invariant_n_positive_case h_n_pos
      have h_rel := invariant_temp_relation h_temp_pos
      -- Since 0 < temp < 10, numDigits temp = 1
      have h_numDigits_temp : numDigits temp = 1 := by
        unfold numDigits
        simp [done_1]
      -- k + 1 - 1 = numDigits n
      rw [h_numDigits_temp] at h_rel
      -- k + 1 - 1 = k when k ≥ 1
      have h_simp : k + 1 - 1 = k := Nat.add_sub_cancel k 1
      rw [h_simp] at h_rel
      exact h_rel

theorem goal_3
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    : armstrongSumAux n i (numDigits n) = armstrongSum n := by
    have h_i_eq : i = numDigits n := goal_2 n require_1 k temp invariant_n_zero_case i temp_1 invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1
    rw [h_i_eq]
    unfold armstrongSum
    rfl

theorem goal_4
    (n : ℕ)
    (require_1 : precondition n)
    (k : ℕ)
    (temp : ℕ)
    (invariant_n_zero_case : n = 0 → temp = 0 ∧ k = 1)
    (i : ℕ)
    (temp_1 : ℕ)
    (remaining : ℕ)
    (sum : ℕ)
    (invariant_k_is_numDigits : i = numDigits n)
    (invariant_armstrong_partial : sum + armstrongSumAux remaining i (numDigits remaining) = armstrongSum n)
    (i_2 : ℕ)
    (sum_1 : ℕ)
    (invariant_k_positive : 1 ≤ k)
    (invariant_temp_relation : 0 < temp → k + numDigits temp - 1 = numDigits n)
    (invariant_n_positive_case : 0 < n → 0 < temp)
    (done_1 : temp < 10)
    (i_1 : k = i ∧ temp = temp_1)
    (done_2 : remaining = 0)
    (i_3 : remaining = i_2 ∧ sum = sum_1)
    : postcondition n (sum_1 == n) := by
    unfold postcondition
    -- From i_3 we get sum = sum_1
    have h_sum_eq : sum = sum_1 := i_3.2
    -- From done_2 we get remaining = 0
    have h_remaining_zero : remaining = 0 := done_2
    -- Compute numDigits 0 = 1
    have h_numDigits_zero : numDigits 0 = 1 := by simp [numDigits]
    -- i is at least 1
    have h_i_pos : 1 ≤ i := by
      rw [invariant_k_is_numDigits]
      unfold numDigits
      split <;> omega
    have h_i_ne_zero : i ≠ 0 := Nat.one_le_iff_ne_zero.mp h_i_pos
    -- Compute armstrongSumAux 0 i 1
    have h_aux_zero : armstrongSumAux 0 i (numDigits 0) = 0 := by
      simp only [h_numDigits_zero]
      unfold armstrongSumAux
      simp only [Nat.one_ne_zero, ↓reduceIte, Nat.sub_self]
      unfold armstrongSumAux
      simp only [↓reduceIte, Nat.add_zero]
      unfold digitAt
      simp only [Nat.pow_zero, Nat.div_one, Nat.zero_mod]
      simp only [Nat.zero_add, Nat.zero_pow h_i_pos]
    -- Substitute remaining = 0 in the invariant
    have h_invariant_sub : sum + armstrongSumAux 0 i (numDigits 0) = armstrongSum n := by
      rw [h_remaining_zero] at invariant_armstrong_partial
      exact invariant_armstrong_partial
    -- Simplify using h_aux_zero
    have h_sum_eq_armstrong : sum = armstrongSum n := by
      simp only [h_aux_zero, Nat.add_zero] at h_invariant_sub
      exact h_invariant_sub
    -- Therefore sum_1 = armstrongSum n
    have h_sum1_eq : sum_1 = armstrongSum n := by
      rw [← h_sum_eq]
      exact h_sum_eq_armstrong
    -- Now prove the biconditional
    rw [h_sum1_eq]
    constructor
    · intro h
      exact beq_iff_eq.mp h
    · intro h
      exact beq_iff_eq.mpr h

prove_correct isArmstrong by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n require_1 k temp invariant_n_zero_case invariant_k_positive invariant_temp_relation invariant_n_positive_case if_pos)
  exact (goal_1 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos)
  exact (goal_2 n require_1 k temp invariant_n_zero_case i temp_1 invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1)
  exact (goal_3 n require_1 k temp invariant_n_zero_case i temp_1 invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1)
  exact (goal_4 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial i_2 sum_1 invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 done_2 i_3)
end Proof
