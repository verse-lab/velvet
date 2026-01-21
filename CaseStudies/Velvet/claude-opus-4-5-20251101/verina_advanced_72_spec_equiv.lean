/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8f19b487-0a67-407c-86c5-252f16d52c9f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat):
  VerinaSpec.singleDigitPrimeFactor_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.singleDigitPrimeFactor_precond n):
  VerinaSpec.singleDigitPrimeFactor_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def singleDigitPrimeFactor_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def singleDigitPrimeFactor_postcond (n : Nat) (result: Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Prop :=
  -- !benchmark @start postcond
  result ∈ [0, 2, 3, 5, 7] ∧
  (result = 0 → (n = 0 ∨ [2, 3, 5, 7].all (n % · ≠ 0))) ∧
  (result ≠ 0 → n ≠ 0 ∧ n % result == 0 ∧ (List.range result).all (fun x => x ∈ [2, 3, 5, 7] → n % x ≠ 0))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- The set of single-digit primes
def singleDigitPrimes : List Nat := [2, 3, 5, 7]

-- Precondition: no restrictions on input
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: result is either 0 (no single-digit prime factor or n <= 1) or the smallest single-digit prime factor
def postcondition (n : Nat) (result : Nat) : Prop :=
  -- Case 1: result is 0 means n <= 1 or no single-digit prime divides n
  (result = 0 ↔ n ≤ 1 ∨ ∀ p ∈ singleDigitPrimes, ¬(p ∣ n)) ∧
  -- Case 2: if result is not 0, it must be a single-digit prime factor and the smallest one
  (result ≠ 0 → (result ∈ singleDigitPrimes ∧ result ∣ n ∧ 
    ∀ p ∈ singleDigitPrimes, p ∣ n → result ≤ p))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.singleDigitPrimeFactor_precond n ↔ LeetProofSpec.precondition n := by
  -- Since both preconditions are True, the equivalence holds trivially.
  simp [VerinaSpec.singleDigitPrimeFactor_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (n : Nat) (result : Nat) (h_precond : VerinaSpec.singleDigitPrimeFactor_precond n):
  VerinaSpec.singleDigitPrimeFactor_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  -- By definition of postcondition, we need to consider the following cases:
  unfold VerinaSpec.singleDigitPrimeFactor_postcond
  unfold LeetProofSpec.postcondition
  simp +decide [ List.mem_cons, List.mem_singleton ];
  -- By definition of singleDigitPrimes, we can replace the LeetProofSpec.singleDigitPrimes with [2, 3, 5, 7] in the equivalences.
  simp [LeetProofSpec.singleDigitPrimes] at *;
  constructor <;> intro h;
  · constructor;
    · grind;
    · grind;
  · by_cases h0 : result = 0 <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
    · grind;
    · grind