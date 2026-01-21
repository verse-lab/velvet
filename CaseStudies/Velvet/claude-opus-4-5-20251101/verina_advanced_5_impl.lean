import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    addTwoNumbers: Add two non-empty linked lists representing non-negative integers in reverse order.

    Natural language breakdown:
    1. Each input list represents a non-negative integer with digits in reverse order (least significant digit first)
    2. Each element in the lists is a single digit (0-9)
    3. The lists are non-empty
    4. The result should also be in reverse order (least significant digit first)
    5. The result represents the sum of the two input numbers
    6. No leading zeros in the representation, except for zero itself which is represented as [0]

    Mathematical formulation:
    - A list [d0, d1, d2, ...] represents the number d0 + d1*10 + d2*100 + ...
    - This is exactly Nat.ofDigits 10 applied to the list
    - The result list should represent the sum of the two input numbers
    - The result should be the canonical digit representation (valid digits, no leading zeros)

    Using Mathlib's Nat.ofDigits:
    - Nat.ofDigits b L converts a list of digits in little-endian order to a number
-/

section Specs
-- Helper: Check if a list represents valid digits (each element is 0-9)
def validDigits (l : List Nat) : Prop :=
  ∀ i : Nat, i < l.length → l[i]! < 10

-- Helper: Check if a digit list has no leading zeros (in reverse representation,
-- this means the last element is non-zero, unless the list is [0])
def noLeadingZeros (l : List Nat) : Prop :=
  l = [0] ∨ (l ≠ [] ∧ l.getLast! ≠ 0)

-- Precondition: Both lists are non-empty, contain valid digits, and have no leading zeros
def precondition (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1.length > 0 ∧
  l2.length > 0 ∧
  validDigits l1 ∧
  validDigits l2 ∧
  noLeadingZeros l1 ∧
  noLeadingZeros l2

-- Postcondition: The result represents the sum of the two input numbers
-- Specified relationally: the numeric value of result equals the sum of input values,
-- and result is in canonical form (valid digits, no leading zeros)
def postcondition (l1 : List Nat) (l2 : List Nat) (result : List Nat) : Prop :=
  -- The result represents the correct sum
  Nat.ofDigits 10 result = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2 ∧
  -- The result contains valid digits
  validDigits result ∧
  -- The result has no leading zeros (canonical form)
  noLeadingZeros result
end Specs

section Impl
method addTwoNumbers (l1 : List Nat) (l2 : List Nat)
  return (result : List Nat)
  require precondition l1 l2
  ensures postcondition l1 l2 result
  do
  -- Use mutable lists and carry for the addition
  let mut i := 0
  let mut carry := 0
  let mut res : List Nat := []
  let len1 := l1.length
  let len2 := l2.length
  let maxLen := if len1 > len2 then len1 else len2
  
  -- Add digit by digit
  while i < maxLen ∨ carry > 0
    -- i is non-negative (always true for Nat)
    invariant "i_bounds" 0 ≤ i
    -- carry is 0 or 1
    invariant "carry_bounded" carry ≤ 1
    -- result list length equals i
    invariant "res_length" res.length = i
    -- all digits in res are valid (< 10)
    invariant "res_valid_digits" validDigits res
    -- core correctness: partial sum relationship
    invariant "sum_invariant" Nat.ofDigits 10 res + carry * (10 ^ i) = Nat.ofDigits 10 (l1.take i) + Nat.ofDigits 10 (l2.take i)
    done_with i >= maxLen ∧ carry = 0
  do
    let d1 := if i < len1 then l1[i]! else 0
    let d2 := if i < len2 then l2[i]! else 0
    let sum := d1 + d2 + carry
    let digit := sum % 10
    carry := sum / 10
    res := res ++ [digit]
    i := i + 1
  
  -- Remove trailing zeros except if the result is just [0]
  let mut trimmed := res
  while trimmed.length > 1 ∧ trimmed.getLast! = 0
    -- length stays positive
    invariant "trimmed_nonempty" trimmed.length ≥ 1
    -- trimmed contains valid digits
    invariant "trimmed_valid" validDigits trimmed
    -- numeric value preserved (trailing zeros don't change value in little-endian)
    invariant "value_preserved" Nat.ofDigits 10 trimmed = Nat.ofDigits 10 res
    done_with trimmed.length <= 1 ∨ trimmed.getLast! ≠ 0
  do
    trimmed := trimmed.dropLast
  
  return trimmed
end Impl

section TestCases
-- Test case 1: Example from problem - 342 + 465 = 807
def test1_l1 : List Nat := [2, 4, 3]
def test1_l2 : List Nat := [5, 6, 4]
def test1_Expected : List Nat := [7, 0, 8]

-- Test case 2: 0 + 0 = 0
def test2_l1 : List Nat := [0]
def test2_l2 : List Nat := [0]
def test2_Expected : List Nat := [0]

-- Test case 3: Large numbers with carry propagation - 9999999 + 9999 = 10009998
def test3_l1 : List Nat := [9, 9, 9, 9, 9, 9, 9]
def test3_l2 : List Nat := [9, 9, 9, 9]
def test3_Expected : List Nat := [8, 9, 9, 9, 0, 0, 0, 1]

-- Test case 4: Different lengths - 321 + 54 = 375
def test4_l1 : List Nat := [1, 2, 3]
def test4_l2 : List Nat := [4, 5]
def test4_Expected : List Nat := [5, 7, 3]

-- Test case 5: Single digits - 5 + 5 = 10
def test5_l1 : List Nat := [5]
def test5_l2 : List Nat := [5]
def test5_Expected : List Nat := [0, 1]

-- Test case 6: No carry - 123 + 456 = 579
def test6_l1 : List Nat := [3, 2, 1]
def test6_l2 : List Nat := [6, 5, 4]
def test6_Expected : List Nat := [9, 7, 5]

-- Test case 7: Adding zero - 123 + 0 = 123
def test7_l1 : List Nat := [3, 2, 1]
def test7_l2 : List Nat := [0]
def test7_Expected : List Nat := [3, 2, 1]

-- Test case 8: Multiple carries - 999 + 1 = 1000
def test8_l1 : List Nat := [9, 9, 9]
def test8_l2 : List Nat := [1]
def test8_Expected : List Nat := [0, 0, 0, 1]

-- Recommend to validate: 1, 3, 5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((addTwoNumbers test1_l1 test1_l2).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((addTwoNumbers test2_l1 test2_l2).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((addTwoNumbers test3_l1 test3_l2).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((addTwoNumbers test4_l1 test4_l2).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((addTwoNumbers test5_l1 test5_l2).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((addTwoNumbers test6_l1 test6_l2).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((addTwoNumbers test7_l1 test7_l2).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((addTwoNumbers test8_l1 test8_l2).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for addTwoNumbers
prove_precondition_decidable_for addTwoNumbers
prove_postcondition_decidable_for addTwoNumbers
derive_tester_for addTwoNumbers
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (List Nat)
    let arg_1 ← Plausible.SampleableExt.interpSample (List Nat)
    let res := addTwoNumbersTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct addTwoNumbers by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (invariant_i_bounds : True)
    (if_pos : (i < if l2.length < l1.length then l1.length else l2.length) ∨ 0 < carry)
    : (((if i < l1.length then l1[i]?.getD 0 else 0) + if i < l2.length then l2[i]?.getD 0 else 0) + carry) / 10 ≤ 1 := by
    -- Extract validDigits from precondition
    obtain ⟨_, _, hv1, hv2, _, _⟩ := require_1
    -- Define the digit values
    set d1 := if i < l1.length then l1[i]?.getD 0 else 0 with hd1_def
    set d2 := if i < l2.length then l2[i]?.getD 0 else 0 with hd2_def
    -- Show d1 ≤ 9
    have hd1_bound : d1 ≤ 9 := by
      simp only [hd1_def]
      split_ifs with h
      · -- When i < l1.length
        rw [List.getD_getElem?]
        simp only [h, dite_true]
        have hvalid := hv1 i h
        simp only [List.getElem!_eq_getElem?_getD] at hvalid
        rw [List.getD_getElem?] at hvalid
        simp only [h, dite_true] at hvalid
        omega
      · omega
    -- Show d2 ≤ 9
    have hd2_bound : d2 ≤ 9 := by
      simp only [hd2_def]
      split_ifs with h
      · -- When i < l2.length
        rw [List.getD_getElem?]
        simp only [h, dite_true]
        have hvalid := hv2 i h
        simp only [List.getElem!_eq_getElem?_getD] at hvalid
        rw [List.getD_getElem?] at hvalid
        simp only [h, dite_true] at hvalid
        omega
      · omega
    -- The sum is at most 19
    have hsum_bound : d1 + d2 + carry ≤ 19 := by omega
    -- 19 / 10 = 1
    have hdiv_bound : 19 / 10 = 1 := by native_decide
    -- Use monotonicity of division
    calc (d1 + d2 + carry) / 10 ≤ 19 / 10 := Nat.div_le_div_right hsum_bound
      _ = 1 := hdiv_bound

theorem goal_1
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (invariant_i_bounds : True)
    (if_pos : (i < if l2.length < l1.length then l1.length else l2.length) ∨ 0 < carry)
    : validDigits (res ++ [(((if i < l1.length then l1[i]?.getD 0 else 0) + if i < l2.length then l2[i]?.getD 0 else 0) + carry) % 10]) := by
    unfold validDigits
    intro j hj
    rw [List.length_append] at hj
    simp only [List.length_singleton] at hj
    by_cases hj_lt : j < res.length
    · -- j is in res
      have h_eq : (res ++ [(((if i < l1.length then l1[i]?.getD 0 else 0) + if i < l2.length then l2[i]?.getD 0 else 0) + carry) % 10])[j]! = res[j]! := by
        simp only [List.getElem!_eq_getElem?_getD]
        rw [List.getElem?_append_left hj_lt]
      rw [h_eq]
      exact invariant_res_valid_digits j hj_lt
    · -- j is the new element (j = res.length)
      have hj_eq : j = res.length := by
        omega
      have h_eq : (res ++ [(((if i < l1.length then l1[i]?.getD 0 else 0) + if i < l2.length then l2[i]?.getD 0 else 0) + carry) % 10])[j]! = (((if i < l1.length then l1[i]?.getD 0 else 0) + if i < l2.length then l2[i]?.getD 0 else 0) + carry) % 10 := by
        simp only [List.getElem!_eq_getElem?_getD]
        rw [hj_eq]
        rw [List.getElem?_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem?_singleton, ↓reduceIte, Option.getD_some]
      rw [h_eq]
      exact Nat.mod_lt _ (by omega : 0 < 10)

theorem goal_2_0
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (invariant_i_bounds : True)
    (if_pos : (i < if l2.length < l1.length then l1.length else l2.length) ∨ 0 < carry)
    (d1 : ℕ := if i < l1.length then l1[i]?.getD 0 else 0)
    (hd1_def : d1 = if i < l1.length then l1[i]?.getD 0 else 0)
    (d2 : ℕ := if i < l2.length then l2[i]?.getD 0 else 0)
    (hd2_def : d2 = if i < l2.length then l2[i]?.getD 0 else 0)
    (sum : ℕ := d1 + d2 + carry)
    (hsum_def : sum = d1 + d2 + carry)
    (digit : ℕ := sum % 10)
    (hdigit_def : digit = sum % 10)
    (carry' : ℕ := sum / 10)
    (hcarry'_def : carry' = sum / 10)
    : Nat.ofDigits 10 (res ++ [digit]) = Nat.ofDigits 10 res + 10 ^ res.length * digit := by
    rw [Nat.ofDigits_append, Nat.ofDigits_singleton]

theorem goal_2_1
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (invariant_i_bounds : True)
    (if_pos : (i < if l2.length < l1.length then l1.length else l2.length) ∨ 0 < carry)
    (d1 : ℕ := if i < l1.length then l1[i]?.getD 0 else 0)
    (hd1_def : d1 = if i < l1.length then l1[i]?.getD 0 else 0)
    (d2 : ℕ := if i < l2.length then l2[i]?.getD 0 else 0)
    (hd2_def : d2 = if i < l2.length then l2[i]?.getD 0 else 0)
    (sum : ℕ := d1 + d2 + carry)
    (hsum_def : sum = d1 + d2 + carry)
    (digit : ℕ := sum % 10)
    (hdigit_def : digit = sum % 10)
    (carry' : ℕ := sum / 10)
    (hcarry'_def : carry' = sum / 10)
    (h_div_mod : sum = digit + carry' * 10)
    (h_ofDigits_append : Nat.ofDigits 10 (res ++ [digit]) = Nat.ofDigits 10 res + 10 ^ res.length * digit)
    (h_ofDigits_singleton : True)
    (h_res_length : res.length = i)
    : Nat.ofDigits 10 (res ++ [digit]) + carry' * 10 ^ (i + 1) = Nat.ofDigits 10 res + sum * 10 ^ i := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_2
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (invariant_i_bounds : True)
    (if_pos : (i < if l2.length < l1.length then l1.length else l2.length) ∨ 0 < carry)
    (d1 : ℕ := if i < l1.length then l1[i]?.getD 0 else 0)
    (hd1_def : d1 = if i < l1.length then l1[i]?.getD 0 else 0)
    (d2 : ℕ := if i < l2.length then l2[i]?.getD 0 else 0)
    (hd2_def : d2 = if i < l2.length then l2[i]?.getD 0 else 0)
    (sum : ℕ := d1 + d2 + carry)
    (hsum_def : sum = d1 + d2 + carry)
    (digit : ℕ := sum % 10)
    (hdigit_def : digit = sum % 10)
    (carry' : ℕ := sum / 10)
    (hcarry'_def : carry' = sum / 10)
    (h_div_mod : sum = digit + carry' * 10)
    (h_lhs_simplified : Nat.ofDigits 10 (res ++ [digit]) + carry' * 10 ^ (i + 1) = Nat.ofDigits 10 res + sum * 10 ^ i)
    (h_ofDigits_append : Nat.ofDigits 10 (res ++ [digit]) = Nat.ofDigits 10 res + 10 ^ res.length * digit)
    (h_ofDigits_singleton : True)
    (h_res_length : res.length = i)
    : Nat.ofDigits 10 res + (d1 + d2 + carry) * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2) + (d1 + d2) * 10 ^ i := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_3
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (invariant_i_bounds : True)
    (if_pos : (i < if l2.length < l1.length then l1.length else l2.length) ∨ 0 < carry)
    (d1 : ℕ := if i < l1.length then l1[i]?.getD 0 else 0)
    (hd1_def : d1 = if i < l1.length then l1[i]?.getD 0 else 0)
    (d2 : ℕ := if i < l2.length then l2[i]?.getD 0 else 0)
    (hd2_def : d2 = if i < l2.length then l2[i]?.getD 0 else 0)
    (sum : ℕ := d1 + d2 + carry)
    (hsum_def : sum = d1 + d2 + carry)
    (digit : ℕ := sum % 10)
    (hdigit_def : digit = sum % 10)
    (carry' : ℕ := sum / 10)
    (hcarry'_def : carry' = sum / 10)
    (h_div_mod : sum = digit + carry' * 10)
    (h_lhs_simplified : Nat.ofDigits 10 (res ++ [digit]) + carry' * 10 ^ (i + 1) = Nat.ofDigits 10 res + sum * 10 ^ i)
    (h_using_invariant : Nat.ofDigits 10 res + (d1 + d2 + carry) * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2) + (d1 + d2) * 10 ^ i)
    (h_ofDigits_append : Nat.ofDigits 10 (res ++ [digit]) = Nat.ofDigits 10 res + 10 ^ res.length * digit)
    (h_ofDigits_singleton : True)
    (h_res_length : res.length = i)
    : Nat.ofDigits 10 (List.take (i + 1) l1) = Nat.ofDigits 10 (List.take i l1) + d1 * 10 ^ i := by
    by_cases h : i < l1.length
    · -- Case: i < l1.length
      rw [List.take_succ_eq_append_getElem h]
      rw [Nat.ofDigits_append]
      have hlen : (List.take i l1).length = i := by
        rw [List.length_take]
        exact Nat.min_eq_left (Nat.le_of_lt h)
      rw [hlen]
      have h_singleton : Nat.ofDigits 10 [l1[i]] = l1[i] := by simp [Nat.ofDigits]
      rw [h_singleton]
      have hd1_eq : d1 = l1[i] := by
        rw [hd1_def]
        simp [h, List.getElem?_eq_getElem h]
      rw [← hd1_eq]
      ring
    · -- Case: i >= l1.length
      have hlen : l1.length ≤ i := Nat.not_lt.mp h
      have htake_succ : List.take (i + 1) l1 = l1 := List.take_of_length_le (Nat.le_trans hlen (Nat.le_succ i))
      have htake_i : List.take i l1 = l1 := List.take_of_length_le hlen
      rw [htake_succ, htake_i]
      have hd1_eq : d1 = 0 := by
        rw [hd1_def]
        simp [h]
      rw [hd1_eq]
      ring

theorem goal_2_4
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (invariant_i_bounds : True)
    (if_pos : (i < if l2.length < l1.length then l1.length else l2.length) ∨ 0 < carry)
    (d1 : ℕ := if i < l1.length then l1[i]?.getD 0 else 0)
    (hd1_def : d1 = if i < l1.length then l1[i]?.getD 0 else 0)
    (d2 : ℕ := if i < l2.length then l2[i]?.getD 0 else 0)
    (hd2_def : d2 = if i < l2.length then l2[i]?.getD 0 else 0)
    (sum : ℕ := d1 + d2 + carry)
    (hsum_def : sum = d1 + d2 + carry)
    (digit : ℕ := sum % 10)
    (hdigit_def : digit = sum % 10)
    (carry' : ℕ := sum / 10)
    (hcarry'_def : carry' = sum / 10)
    (h_div_mod : sum = digit + carry' * 10)
    (h_lhs_simplified : Nat.ofDigits 10 (res ++ [digit]) + carry' * 10 ^ (i + 1) = Nat.ofDigits 10 res + sum * 10 ^ i)
    (h_using_invariant : Nat.ofDigits 10 res + (d1 + d2 + carry) * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2) + (d1 + d2) * 10 ^ i)
    (h_take_l1 : Nat.ofDigits 10 (List.take (i + 1) l1) = Nat.ofDigits 10 (List.take i l1) + d1 * 10 ^ i)
    (h_ofDigits_append : Nat.ofDigits 10 (res ++ [digit]) = Nat.ofDigits 10 res + 10 ^ res.length * digit)
    (h_ofDigits_singleton : True)
    (h_res_length : res.length = i)
    : Nat.ofDigits 10 (List.take (i + 1) l2) = Nat.ofDigits 10 (List.take i l2) + d2 * 10 ^ i := by
    by_cases hi : i < l2.length
    · -- Case: i < l2.length
      have h_take_succ : List.take (i + 1) l2 = List.take i l2 ++ [l2[i]] := List.take_succ_eq_append_getElem hi
      rw [h_take_succ, Nat.ofDigits_append, Nat.ofDigits_singleton]
      have h_len_take : (List.take i l2).length = i := by
        rw [List.length_take]
        exact Nat.min_eq_left (Nat.le_of_lt hi)
      rw [h_len_take]
      have h_d2_eq : d2 = l2[i] := by
        simp only [hd2_def, hi, ↓reduceIte]
        rw [List.getElem?_eq_getElem hi, Option.getD_some]
      rw [h_d2_eq]
      ring
    · -- Case: i >= l2.length
      push_neg at hi
      have h_take_i : List.take i l2 = l2 := List.take_of_length_le hi
      have h_take_i1 : List.take (i + 1) l2 = l2 := List.take_of_length_le (Nat.le_trans hi (Nat.le_succ i))
      rw [h_take_i, h_take_i1]
      have h_d2_zero : d2 = 0 := by
        simp only [hd2_def, hi, ↓reduceIte, not_lt.mpr hi]
      rw [h_d2_zero]
      ring

theorem goal_2_5
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (invariant_i_bounds : True)
    (if_pos : (i < if l2.length < l1.length then l1.length else l2.length) ∨ 0 < carry)
    (d1 : ℕ := if i < l1.length then l1[i]?.getD 0 else 0)
    (hd1_def : d1 = if i < l1.length then l1[i]?.getD 0 else 0)
    (d2 : ℕ := if i < l2.length then l2[i]?.getD 0 else 0)
    (hd2_def : d2 = if i < l2.length then l2[i]?.getD 0 else 0)
    (sum : ℕ := d1 + d2 + carry)
    (hsum_def : sum = d1 + d2 + carry)
    (digit : ℕ := sum % 10)
    (hdigit_def : digit = sum % 10)
    (carry' : ℕ := sum / 10)
    (hcarry'_def : carry' = sum / 10)
    (h_div_mod : sum = digit + carry' * 10)
    (h_lhs_simplified : Nat.ofDigits 10 (res ++ [digit]) + carry' * 10 ^ (i + 1) = Nat.ofDigits 10 res + sum * 10 ^ i)
    (h_using_invariant : Nat.ofDigits 10 res + (d1 + d2 + carry) * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2) + (d1 + d2) * 10 ^ i)
    (h_take_l1 : Nat.ofDigits 10 (List.take (i + 1) l1) = Nat.ofDigits 10 (List.take i l1) + d1 * 10 ^ i)
    (h_take_l2 : Nat.ofDigits 10 (List.take (i + 1) l2) = Nat.ofDigits 10 (List.take i l2) + d2 * 10 ^ i)
    (h_ofDigits_append : Nat.ofDigits 10 (res ++ [digit]) = Nat.ofDigits 10 res + 10 ^ res.length * digit)
    (h_ofDigits_singleton : True)
    (h_res_length : res.length = i)
    : Nat.ofDigits 10 (List.take (i + 1) l1) + Nat.ofDigits 10 (List.take (i + 1) l2) = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2) + (d1 + d2) * 10 ^ i := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (invariant_i_bounds : True)
    (if_pos : (i < if l2.length < l1.length then l1.length else l2.length) ∨ 0 < carry)
    : Nat.ofDigits 10 (res ++ [(((if i < l1.length then l1[i]?.getD 0 else 0) + if i < l2.length then l2[i]?.getD 0 else 0) + carry) % 10]) + (((if i < l1.length then l1[i]?.getD 0 else 0) + if i < l2.length then l2[i]?.getD 0 else 0) + carry) / 10 * 10 ^ (i + 1) = Nat.ofDigits 10 (List.take (i + 1) l1) + Nat.ofDigits 10 (List.take (i + 1) l2) := by
    -- Define the digit values for clarity
    set d1 := if i < l1.length then l1[i]?.getD 0 else 0 with hd1_def
    set d2 := if i < l2.length then l2[i]?.getD 0 else 0 with hd2_def
    set sum := d1 + d2 + carry with hsum_def
    set digit := sum % 10 with hdigit_def
    set carry' := sum / 10 with hcarry'_def
    -- Step 1: Use Nat.ofDigits_append to expand the LHS
    have h_ofDigits_append : Nat.ofDigits 10 (res ++ [digit]) = Nat.ofDigits 10 res + 10 ^ res.length * Nat.ofDigits 10 [digit] := by
      (try simp at *; expose_names); exact (goal_2_0 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant invariant_i_bounds if_pos d1 hd1_def d2 hd2_def sum hsum_def digit hdigit_def carry' hcarry'_def); done
    -- Step 2: Simplify Nat.ofDigits of singleton list
    have h_ofDigits_singleton : Nat.ofDigits 10 [digit] = digit := by
      (try simp at *; expose_names); exact hdigit_def; done
    -- Step 3: Use res.length = i to simplify the power
    have h_res_length : 10 ^ res.length = 10 ^ i := by
      (try simp at *; expose_names); exact invariant_res_length; done
    -- Step 4: The division/modulo identity: sum = digit + carry' * 10
    have h_div_mod : sum = digit + carry' * 10 := by
      (try simp at *; expose_names); exact Eq.symm (Nat.mod_add_div' sum 10); done
    -- Step 5: Rewrite LHS using the above facts
    have h_lhs_simplified : Nat.ofDigits 10 (res ++ [digit]) + carry' * 10 ^ (i + 1) = Nat.ofDigits 10 res + sum * 10 ^ i := by
      (try simp at *; expose_names); exact (goal_2_1 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant invariant_i_bounds if_pos d1 hd1_def d2 hd2_def sum hsum_def digit hdigit_def carry' hcarry'_def h_div_mod h_ofDigits_append h_ofDigits_singleton h_res_length); done
    -- Step 6: Expand sum and use the invariant
    have h_using_invariant : Nat.ofDigits 10 res + (d1 + d2 + carry) * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2) + (d1 + d2) * 10 ^ i := by
      (try simp at *; expose_names); exact (goal_2_2 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant invariant_i_bounds if_pos d1 hd1_def d2 hd2_def sum hsum_def digit hdigit_def carry' hcarry'_def h_div_mod h_lhs_simplified h_ofDigits_append h_ofDigits_singleton h_res_length); done
    -- Step 7: Relate take (i+1) to take i for l1
    have h_take_l1 : Nat.ofDigits 10 (List.take (i + 1) l1) = Nat.ofDigits 10 (List.take i l1) + d1 * 10 ^ i := by
      (try simp at *; expose_names); exact (goal_2_3 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant invariant_i_bounds if_pos d1 hd1_def d2 hd2_def sum hsum_def digit hdigit_def carry' hcarry'_def h_div_mod h_lhs_simplified h_using_invariant h_ofDigits_append h_ofDigits_singleton h_res_length); done
    -- Step 8: Relate take (i+1) to take i for l2
    have h_take_l2 : Nat.ofDigits 10 (List.take (i + 1) l2) = Nat.ofDigits 10 (List.take i l2) + d2 * 10 ^ i := by
      (try simp at *; expose_names); exact (goal_2_4 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant invariant_i_bounds if_pos d1 hd1_def d2 hd2_def sum hsum_def digit hdigit_def carry' hcarry'_def h_div_mod h_lhs_simplified h_using_invariant h_take_l1 h_ofDigits_append h_ofDigits_singleton h_res_length); done
    -- Step 9: Combine to show RHS equals the expanded form
    have h_rhs_simplified : Nat.ofDigits 10 (List.take (i + 1) l1) + Nat.ofDigits 10 (List.take (i + 1) l2) = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2) + (d1 + d2) * 10 ^ i := by
      (try simp at *; expose_names); exact (goal_2_5 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant invariant_i_bounds if_pos d1 hd1_def d2 hd2_def sum hsum_def digit hdigit_def carry' hcarry'_def h_div_mod h_lhs_simplified h_using_invariant h_take_l1 h_take_l2 h_ofDigits_append h_ofDigits_singleton h_res_length); done
    -- Final: Combine all steps to prove the goal
    simp only [← hdigit_def, ← hcarry'_def, ← hd1_def, ← hd2_def, ← hsum_def] at h_lhs_simplified h_using_invariant h_rhs_simplified h_take_l1 h_take_l2
    omega

theorem goal_3
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    : validDigits [] := by
    unfold validDigits
    intro i hi
    simp [List.length_nil] at hi

theorem goal_4
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    : Nat.ofDigits 10 [] + 0 * 10 ^ 0 = Nat.ofDigits 10 (List.take 0 l1) + Nat.ofDigits 10 (List.take 0 l2) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_5
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (a_1 : carry = 0)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (res_1 : List ℕ)
    (trimmed : List ℕ)
    (invariant_trimmed_valid : validDigits trimmed)
    (invariant_value_preserved : Nat.ofDigits 10 trimmed = Nat.ofDigits 10 res_1)
    (invariant_i_bounds : True)
    (a : (if l2.length < l1.length then l1.length else l2.length) ≤ i)
    (i_3 : carry = i_1 ∧ i = i_2 ∧ res = res_1)
    (invariant_trimmed_nonempty : 1 ≤ trimmed.length)
    (a_2 : 1 < trimmed.length)
    (a_3 : trimmed.getLast?.getD 0 = 0)
    : validDigits trimmed.dropLast := by
    unfold validDigits at *
    intro j hj
    have hj_orig : j < trimmed.length := by
      simp [List.length_dropLast] at hj
      omega
    have hj' : j < trimmed.dropLast.length := hj
    have h_elem_eq : trimmed.dropLast[j]'hj' = trimmed[j]'hj_orig := List.getElem_dropLast hj'
    have h_getElem!_dropLast : trimmed.dropLast[j]! = trimmed.dropLast[j]'hj' := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    have h_getElem!_orig : trimmed[j]! = trimmed[j]'hj_orig := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj_orig]
    rw [h_getElem!_dropLast, h_elem_eq, ← h_getElem!_orig]
    exact invariant_trimmed_valid j hj_orig

theorem goal_6
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (a_1 : carry = 0)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (res_1 : List ℕ)
    (trimmed : List ℕ)
    (invariant_trimmed_valid : validDigits trimmed)
    (invariant_value_preserved : Nat.ofDigits 10 trimmed = Nat.ofDigits 10 res_1)
    (invariant_i_bounds : True)
    (a : (if l2.length < l1.length then l1.length else l2.length) ≤ i)
    (i_3 : carry = i_1 ∧ i = i_2 ∧ res = res_1)
    (invariant_trimmed_nonempty : 1 ≤ trimmed.length)
    (a_2 : 1 < trimmed.length)
    (a_3 : trimmed.getLast?.getD 0 = 0)
    : Nat.ofDigits 10 trimmed.dropLast = Nat.ofDigits 10 res_1 := by
    rw [← invariant_value_preserved]
    have h_nonempty : trimmed ≠ [] := by
      intro h
      simp [h] at invariant_trimmed_nonempty
    -- Show that getLast? is some for nonempty list
    have h_last_isSome : trimmed.getLast?.isSome = true := List.getLast?_isSome.mpr h_nonempty
    -- Get the value from Option.isSome
    have h_getLast_some : ∃ x, trimmed.getLast? = some x := by
      cases h_eq : trimmed.getLast? with
      | none => simp [h_eq] at h_last_isSome
      | some val => exact ⟨val, rfl⟩
    obtain ⟨last_val, h_last_eq⟩ := h_getLast_some
    have h_last_is_zero : last_val = 0 := by
      simp only [h_last_eq, Option.getD_some] at a_3
      exact a_3
    -- Use dropLast_append_getLast? 
    have h_decompose : trimmed.dropLast ++ [last_val] = trimmed := by
      exact List.dropLast_append_getLast? last_val h_last_eq
    rw [← h_decompose]
    rw [Nat.ofDigits_append]
    rw [h_last_is_zero]
    simp [Nat.ofDigits_singleton]

theorem goal_7
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (a_1 : carry = 0)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (res_1 : List ℕ)
    (invariant_i_bounds : True)
    (a : (if l2.length < l1.length then l1.length else l2.length) ≤ i)
    (i_3 : carry = i_1 ∧ i = i_2 ∧ res = res_1)
    : 1 ≤ res_1.length := by
    -- From i_3, we have res = res_1
    obtain ⟨_, _, h_res_eq⟩ := i_3
    -- So res_1.length = res.length = i
    rw [← h_res_eq, invariant_res_length]
    -- From precondition, l1.length > 0
    unfold precondition at require_1
    obtain ⟨h_l1_pos, h_l2_pos, _⟩ := require_1
    -- The max of l1.length and l2.length is ≥ 1
    have h_max_pos : 1 ≤ (if l2.length < l1.length then l1.length else l2.length) := by
      split_ifs with h
      · exact h_l1_pos
      · exact h_l2_pos
    -- And this max is ≤ i
    exact Nat.le_trans h_max_pos a

theorem goal_8
    (l1 : List ℕ)
    (l2 : List ℕ)
    (require_1 : precondition l1 l2)
    (carry : ℕ)
    (i : ℕ)
    (res : List ℕ)
    (invariant_carry_bounded : carry ≤ 1)
    (invariant_res_length : res.length = i)
    (invariant_res_valid_digits : validDigits res)
    (invariant_sum_invariant : Nat.ofDigits 10 res + carry * 10 ^ i = Nat.ofDigits 10 (List.take i l1) + Nat.ofDigits 10 (List.take i l2))
    (a_1 : carry = 0)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (res_1 : List ℕ)
    (trimmed : List ℕ)
    (invariant_trimmed_valid : validDigits trimmed)
    (invariant_value_preserved : Nat.ofDigits 10 trimmed = Nat.ofDigits 10 res_1)
    (invariant_i_bounds : True)
    (a : (if l2.length < l1.length then l1.length else l2.length) ≤ i)
    (i_3 : carry = i_1 ∧ i = i_2 ∧ res = res_1)
    (invariant_trimmed_nonempty : 1 ≤ trimmed.length)
    (done_2 : trimmed.length ≤ 1 ∨ ¬trimmed.getLast?.getD 0 = 0)
    : postcondition l1 l2 trimmed := by
  unfold postcondition
  obtain ⟨_, _, hres_eq⟩ := i_3
  constructor
  · -- Nat.ofDigits 10 trimmed = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2
    rw [invariant_value_preserved, ← hres_eq]
    have h1 : l1.length ≤ i := by
      split_ifs at a with h
      · exact a
      · exact Nat.le_of_not_lt h |>.trans a
    have h2 : l2.length ≤ i := by
      split_ifs at a with h
      · exact Nat.le_of_lt h |>.trans a
      · exact a
    rw [List.take_of_length_le h1, List.take_of_length_le h2] at invariant_sum_invariant
    simp [a_1] at invariant_sum_invariant
    exact invariant_sum_invariant
  constructor
  · -- validDigits trimmed
    exact invariant_trimmed_valid
  · -- noLeadingZeros trimmed
    unfold noLeadingZeros
    cases done_2 with
    | inl hlen =>
      -- trimmed.length ≤ 1, combined with invariant_trimmed_nonempty gives length = 1
      have hlen_eq : trimmed.length = 1 := Nat.le_antisymm hlen invariant_trimmed_nonempty
      cases trimmed with
      | nil => simp at hlen_eq
      | cons x xs =>
        simp at hlen_eq
        subst hlen_eq
        by_cases hx : x = 0
        · left; simp [hx]
        · right
          constructor
          · simp
          · simp [List.getLast!]
            exact hx
    | inr hne =>
      -- ¬trimmed.getLast?.getD 0 = 0, meaning getLast! ≠ 0
      right
      constructor
      · intro h
        rw [h] at invariant_trimmed_nonempty
        simp at invariant_trimmed_nonempty
      · have hne' : trimmed ≠ [] := by
          intro h
          rw [h] at invariant_trimmed_nonempty
          simp at invariant_trimmed_nonempty
        have hlast_eq : trimmed.getLast? = some (trimmed.getLast hne') := List.getLast?_eq_getLast hne'
        rw [hlast_eq, Option.getD_some] at hne
        have : trimmed.getLast! = trimmed.getLast hne' := by
          cases trimmed with
          | nil => exact absurd rfl hne'
          | cons x xs => rfl
        rw [this]
        exact hne


prove_correct addTwoNumbers by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant invariant_i_bounds if_pos)
  exact (goal_1 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant invariant_i_bounds if_pos)
  exact (goal_2 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant invariant_i_bounds if_pos)
  exact (goal_3 l1 l2 require_1)
  exact (goal_4 l1 l2 require_1)
  exact (goal_5 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant a_1 i_1 i_2 res_1 trimmed invariant_trimmed_valid invariant_value_preserved invariant_i_bounds a i_3 invariant_trimmed_nonempty a_2 a_3)
  exact (goal_6 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant a_1 i_1 i_2 res_1 trimmed invariant_trimmed_valid invariant_value_preserved invariant_i_bounds a i_3 invariant_trimmed_nonempty a_2 a_3)
  exact (goal_7 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant a_1 i_1 i_2 res_1 invariant_i_bounds a i_3)
  exact (goal_8 l1 l2 require_1 carry i res invariant_carry_bounded invariant_res_length invariant_res_valid_digits invariant_sum_invariant a_1 i_1 i_2 res_1 trimmed invariant_trimmed_valid invariant_value_preserved invariant_i_bounds a i_3 invariant_trimmed_nonempty done_2)
end Proof
