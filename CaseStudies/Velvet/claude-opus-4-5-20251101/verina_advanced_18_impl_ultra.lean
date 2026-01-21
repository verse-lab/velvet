/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 72ef8e95-fdac-403a-b9c5-532c7373689e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem goal_1_4_4_0
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
    : armstrongSumAux m' k' j = armstrongSumAux m' k' (j - 1) + digitAt m' (j - 1) ^ k'

- theorem goal_1_4_4_2
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
    : armstrongSumAux m' k' j = digitAt m' 0 ^ k' + armstrongSumAux (m' / 10) k' (j - 1)

- theorem goal_1_4_6_0
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
    : 1 ≤ numDigits (remaining / 10)

- theorem goal_1_4_6_1
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
    : armstrongSumAux remaining i (numDigits (remaining / 10)) = digitAt remaining 0 ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0

- theorem goal_1_4_6_2
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
    : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) + digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i

- theorem goal_1_4_6_3
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
    : armstrongSumAux remaining i (numDigits (remaining / 10)) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1)

- theorem goal_1_4_6_4
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
    : digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i ≤ armstrongSumAux (remaining / 10) i (numDigits (remaining / 10))

- theorem goal_1_4_7_0
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
    : armstrongSumAux remaining i (numDigits remaining) = armstrongSumAux remaining i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i

- theorem goal_1_4_7_1
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
    : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ∨ numDigits (remaining / 10) = 0

- theorem goal_1_4_7_2
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
    : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) + digitAt remaining (numDigits (remaining / 10)) ^ i

- theorem goal_1_4_7_3
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
    : 1 ≤ numDigits (remaining / 10)

- theorem goal_1_4_7_4
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
    : digitAt remaining (numDigits (remaining / 10)) = digitAt (remaining / 10) (numDigits (remaining / 10) - 1)

- theorem goal_1_4_7_5
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
    : armstrongSumAux (remaining / 10) i (numDigits (remaining / 10)) = armstrongSumAux (remaining / 10) i (numDigits (remaining / 10) - 1) + digitAt (remaining / 10) (numDigits (remaining / 10) - 1) ^ i

- theorem goal_1_4_7_6
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
    : armstrongSumAux remaining i (numDigits remaining) = (remaining % 10) ^ i + armstrongSumAux (remaining / 10) i (numDigits (remaining / 10))
-/

import Lean
import Mathlib.Tactic


-- Specs Section
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

-- Proof Section
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
    -- Substitute $j = j' + 1$ into the recurrence relation.
    rw [h_j_eq];
    -- By definition of armstrongSumAux, we have armstrongSumAux m' k' (j' + 1) = armstrongSumAux m' k' j' + digitAt m' j' ^ k'.
    rw [armstrongSumAux];
    -- Since $j' + 1 \neq 0$, the if statement simplifies to the else part.
    simp [Nat.succ_ne_zero]

/- Aristotle failed to find a proof. -/
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
    have h_armstrongSumAux_shift : ∀ m k j, armstrongSumAux m k (j + 1) = armstrongSumAux m k j + digitAt m j ^ k := by
      -- By definition of `armstrongSumAux`, we have `armstrongSumAux m k (j + 1) = armstrongSumAux m k j + (digitAt m j) ^ k` for any `m`, `k`, and `j`.
      intros m k j
      rw [armstrongSumAux];
      rfl;
    have h_armstrongSumAux_shift : ∀ m k j, armstrongSumAux m k j = ∑ i ∈ Finset.range j, digitAt m i ^ k := by
      intro m k j; induction' j with j ih <;> simp +decide [ *, Finset.sum_range_succ ] ;
    simp_all +decide [ Finset.sum_range_succ' ];
    have := ‹∀ m k j, ∑ x ∈ Finset.range j, digitAt ( m / 10 ) x ^ k + digitAt m 0 ^ k = ∑ i ∈ Finset.range j, digitAt m i ^ k + digitAt m j ^ k› m' k' j'; simp_all +decide [ add_comm, Finset.sum_range_succ ] ;

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
    unfold numDigits; aesop;

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
    -- Apply the hypothesis `h_armstrongSumAux_shift` with `m = remaining`, `k = i`, and `j = numDigits (remaining / 10)`.
    apply h_armstrongSumAux_shift remaining i (numDigits (remaining / 10)) (by linarith)

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
    -- Apply the definition of `armstrongSumAux` with `j = numDigits (remaining / 10)`.
    have h_armstrongSumAux_def : ∀ m k j, j > 0 → armstrongSumAux m k j = armstrongSumAux m k (j - 1) + digitAt m (j - 1) ^ k := by
      intros m k j hj_pos;
      induction' j with j ih generalizing m k;
      · contradiction;
      · unfold armstrongSumAux; simp +decide [ * ] ;
        cases j <;> simp +decide [ * ];
    exact h_armstrongSumAux_def _ _ _ h_numDigits_div_ge_1

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
    grind

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
    -- Rearrange h_aux_unfold_div to isolate the digit term on one side.
    rw [h_aux_unfold_div]
    simp

/- Aristotle failed to find a proof. -/
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
    grind

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
    cases h : numDigits ( remaining / 10 ) <;> simp +decide [ *, Nat.pow_succ', ← Nat.div_div_eq_div_mul ]

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
    -- Substitute h_armstrongSumAux_eq into h_lhs_step1 to conclude the proof.
    rw [h_lhs_step1, h_armstrongSumAux_eq]

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
    -- Since `remaining` is positive and not less than 10, its digits must be at least 2.
    have h_numDigits_ge_two : 2 ≤ numDigits remaining := by
      by_cases h_remaining_lt_10 : remaining < 10;
      · -- Since `remaining` is less than 10, `remaining / 10` is 0. The `numDigits` of 0 is 1, so `numDigits (remaining / 10) = 1`.
        have h_numDigits_zero : numDigits (remaining / 10) = 1 := by
          interval_cases remaining <;> trivial;
        linarith [ Nat.sub_add_cancel h_numDigits_remaining_pos ];
      · have h_numDigits_ge_two : ∀ m, 10 ≤ m → 2 ≤ numDigits m := by
          intros m hm
          have h_numDigits_ge_two : ∀ m, 10 ≤ m → 2 ≤ numDigits m := by
            intros m hm
            induction' m using Nat.strong_induction_on with m ih
            unfold numDigits; simp +arith +decide [ * ] ;
            -- Since $m \geq 10$, we have $m / 10 \geq 1$, and thus $numDigits (m / 10) \geq 1$.
            have h_numDigits_ge_one : 1 ≤ numDigits (m / 10) := by
              exact Nat.pos_of_ne_zero ( by unfold numDigits; split_ifs <;> omega ) ;
            grind
          exact h_numDigits_ge_two m hm;
        exact h_numDigits_ge_two remaining ( le_of_not_gt h_remaining_lt_10 );
    omega

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
    -- Since `numDigits (remaining / 10)` is not zero, we can apply the first part of `h_digitAt_shift_applied`.
    apply Or.resolve_right h_digitAt_shift_applied h_numDigits_div_ne_zero

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
    convert goal_1_4_6_3 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_case_lt_10 h_numDigits_div_pos h_numDigits_div_ne_zero using 1;
    -- Apply the hypothesis `h_digitAt_shift_applied` with `j = numDigits (remaining / 10) - 1` to conclude the proof.
    apply Iff.intro;
    · grind;
    · intro h;
      apply goal_1_4_6_2 n require_1 k temp invariant_n_zero_case i temp_1 remaining sum invariant_k_is_numDigits invariant_armstrong_partial invariant_k_positive invariant_temp_relation invariant_n_positive_case done_1 i_1 if_pos h_remaining_pos h_numDigits_remaining_pos h_numDigits_remaining_ne_zero h_digitAt_zero h_armstrongSumAux_unfold h_cases h_numDigits_zero h_armstrongSumAux_one h_armstrongSumAux_zero h_digitAt_shift h_armstrongSumAux_shift h_ge_10_case h_numDigits_sub h_digitAt_last h_case_lt_10 h_numDigits_div_pos h_numDigits_div_ne_zero;
      · grind;
      · rw [h_digitAt_zero];
      · exact Nat.succ_pred_eq_of_pos h_numDigits_div_pos;
      · trivial

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
    grind

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
