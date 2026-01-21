/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 58f2a4a9-67f5-4300-885f-8aeee548e61c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (digits : List Nat):
  VerinaSpec.binaryToDecimal_precond digits ↔ LeetProofSpec.precondition digits

- theorem postcondition_equiv (digits : List Nat) (result : Nat) (h_precond : VerinaSpec.binaryToDecimal_precond digits):
  VerinaSpec.binaryToDecimal_postcond digits result h_precond ↔ LeetProofSpec.postcondition digits result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def binaryToDecimal_precond (digits : List Nat) : Prop :=
  -- !benchmark @start precond
  digits.all (fun d => d = 0 ∨ d = 1)

-- !benchmark @end precond

@[reducible]
def binaryToDecimal_postcond (digits : List Nat) (result: Nat) (h_precond : binaryToDecimal_precond (digits)) : Prop :=
  -- !benchmark @start postcond
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

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

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (digits : List Nat):
  VerinaSpec.binaryToDecimal_precond digits ↔ LeetProofSpec.precondition digits := by
  aesop

theorem postcondition_equiv (digits : List Nat) (result : Nat) (h_precond : VerinaSpec.binaryToDecimal_precond digits):
  VerinaSpec.binaryToDecimal_postcond digits result h_precond ↔ LeetProofSpec.postcondition digits result := by
  constructor <;> intro h;
  · -- By definition of binaryToDecimal_postcond, we know that result is equal to the foldl of the digits with the function that multiplies by 2 and adds the bit.
    have h_foldl : result = List.foldl (λ acc bit => acc * 2 + bit) 0 digits := by
      grind;
    -- By definition of foldl, we can prove the positional value property by induction on the list of digits.
    have h_ind : ∀ (ds : List ℕ), (∀ d ∈ ds, d = 0 ∨ d = 1) → ∀ i, i < List.length ds → (List.foldl (fun acc bit => acc * 2 + bit) 0 ds).testBit (List.length ds - 1 - i) = (ds[i]! == 1) := by
      -- We'll use induction on the list of digits.
      intro ds hds
      induction' ds using List.reverseRecOn with ds ih;
      · decide +revert;
      · -- By definition of foldl, we can split the list into the prefix and the last element.
        simp [List.foldl_append, List.foldl_cons];
        intro i hi; rcases hi with ( hi | hi ) <;> simp_all +decide [ Nat.testBit ] ;
        · cases hds ih ( Or.inr rfl ) <;> simp +decide [ * ];
        · cases hds ih ( Or.inr rfl ) <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ];
          · rcases k : List.length ds - i <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
            · omega;
            · grind +ring;
          · rcases k : ds.length - i with ( _ | k ) <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
            · omega;
            · simp_all +decide [ Nat.add_div, Nat.mul_div_assoc ];
              grind;
    have h_foldl_zero : ∀ (ds : List ℕ), (∀ d ∈ ds, d = 0 ∨ d = 1) → ∀ j, j ≥ List.length ds → (List.foldl (fun acc bit => acc * 2 + bit) 0 ds).testBit j = false := by
      intros ds hds j hj
      induction' ds using List.reverseRecOn with ds ih generalizing j;
      · induction j <;> simp_all +decide [ Nat.testBit ];
      · simp_all +decide [ Nat.testBit ];
        rcases j with ( _ | j ) <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ];
        rw [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
        cases hds ih ( Or.inr rfl ) <;> simp_all +decide [ Nat.add_div ];
    unfold LeetProofSpec.postcondition; aesop;
  · -- By definition of postcondition, we know that result.testBit (digits.length - 1 - i) = (digits[i]! == 1) for all i < digits.length.
    have h_bit : ∀ i < digits.length, result.testBit (digits.length - 1 - i) = (digits[i]! == 1) := by
      exact h.2.1;
    -- By definition of postcondition, we know that result.testBit j = false for all j ≥ digits.length.
    have h_bit_false : ∀ j ≥ digits.length, result.testBit j = false := by
      exact h.2.2;
    -- By definition of postcondition, we know that result is equal to the sum of the binary digits multiplied by their respective powers of 2.
    have h_sum : result = ∑ i ∈ Finset.range digits.length, (if digits[i]! = 1 then 2 ^ (digits.length - 1 - i) else 0) := by
      have h_sum : result = ∑ i ∈ Finset.range (digits.length), (if result.testBit i then 2 ^ i else 0) := by
        have h_sum : ∀ n, result = ∑ i ∈ Finset.range n, (if result.testBit i then 2 ^ i else 0) + 2 ^ n * (result / 2 ^ n) := by
          intro n;
          induction' n with n ih;
          · norm_num;
          · rw [ Finset.sum_range_succ, pow_succ' ];
            split_ifs <;> simp +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ] at *;
            · rw [ show result / ( 2 * 2 ^ n ) = result / 2 ^ n / 2 by rw [ Nat.div_div_eq_div_mul ] ; ring ] ; nlinarith [ Nat.mod_add_div ( result / 2 ^ n ) 2, pow_pos ( zero_lt_two' ℕ ) n ] ;
            · rw [ show result / ( 2 * 2 ^ n ) = result / 2 ^ n / 2 by rw [ Nat.div_div_eq_div_mul ] ; ring ] ; nlinarith [ Nat.mod_add_div ( result / 2 ^ n ) 2, pow_pos ( zero_lt_two' ℕ ) n ];
        -- Since for all $j \geq \text{digits.length}$, $\text{result.testBit } j = \text{false}$, we have $\text{result} / 2^{\text{digits.length}} = 0$.
        have h_div_zero : result / 2 ^ digits.length = 0 := by
          rw [ Nat.div_eq_of_lt ];
          exact?;
        simpa [ h_div_zero ] using h_sum digits.length;
      rw [ h_sum, ← Finset.sum_range_reflect ];
      -- By substituting h_bit into the sum, we can replace result.testBit (digits.length - 1 - j) with digits[j]! == 1.
      apply Finset.sum_congr rfl
      intro j hj
      simp [h_bit j (Finset.mem_range.mp hj)];
    -- By definition of `List.foldl`, we can rewrite the right-hand side of the equation.
    have h_foldl : List.foldl (fun acc bit => acc * 2 + bit) 0 digits = ∑ i ∈ Finset.range digits.length, (digits[i]! : ℕ) * 2 ^ (digits.length - 1 - i) := by
      have h_foldl : ∀ (ds : List ℕ), List.foldl (fun acc bit => acc * 2 + bit) 0 ds = ∑ i ∈ Finset.range ds.length, (ds[i]! : ℕ) * 2 ^ (ds.length - 1 - i) := by
        intro ds; induction' ds using List.reverseRecOn with ds ih <;> simp +arith +decide [ *, Finset.sum_range_succ ] ;
        simp_all +decide [ mul_comm, Finset.sum_range, List.getElem?_append ];
        rw [ add_comm, Finset.mul_sum _ _ _ ];
        exact congrArg₂ _ ( Finset.sum_congr rfl fun i hi => by rw [ ← mul_assoc, ← pow_succ', tsub_right_comm, Nat.sub_add_cancel ( Nat.succ_le_of_lt ( Nat.sub_pos_of_lt ( Fin.is_lt i ) ) ) ] ) rfl;
      apply h_foldl;
    -- By definition of `digits`, we know that `digits[i]!` is either 0 or 1 for all `i`.
    have h_digits : ∀ i < digits.length, digits[i]! = 0 ∨ digits[i]! = 1 := by
      unfold VerinaSpec.binaryToDecimal_precond at h_precond; aesop;
    exact ⟨ Nat.sub_eq_zero_of_le <| h_sum.symm ▸ h_foldl.symm ▸ Finset.sum_le_sum fun i hi => by cases h_digits i ( Finset.mem_range.mp hi ) <;> simp +decide [ * ], Nat.sub_eq_zero_of_le <| h_foldl.symm ▸ h_sum.symm ▸ Finset.sum_le_sum fun i hi => by cases h_digits i ( Finset.mem_range.mp hi ) <;> simp +decide [ * ] ⟩