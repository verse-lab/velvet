/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7332b439-af1b-4826-993f-b5ef0695256e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat):
  VerinaSpec.isPrime_precond n ↔ LeetProofSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Bool) (h_precond : VerinaSpec.isPrime_precond n):
  VerinaSpec.isPrime_postcond n result h_precond ↔ LeetProofSpec.postcondition n result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isPrime_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 2

-- !benchmark @end precond

def isPrime_postcond (n : Nat) (result: Bool) (h_precond : isPrime_precond (n)) :=
  -- !benchmark @start postcond
  (result → (List.range' 2 (n - 2)).all (fun k => n % k ≠ 0)) ∧
  (¬ result → (List.range' 2 (n - 2)).any (fun k => n % k = 0))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: n must be at least 2
def precondition (n : Nat) : Prop :=
  n ≥ 2

-- Postcondition: result is true iff n is prime
-- Using Mathlib's Nat.Prime which states:
-- A natural number is prime if it is greater than 1 and has no divisors other than 1 and itself
def postcondition (n : Nat) (result : Bool) : Prop :=
  result = true ↔ Nat.Prime n

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat):
  VerinaSpec.isPrime_precond n ↔ LeetProofSpec.precondition n := by
  exact Iff.rfl

theorem postcondition_equiv (n : Nat) (result : Bool) (h_precond : VerinaSpec.isPrime_precond n):
  VerinaSpec.isPrime_postcond n result h_precond ↔ LeetProofSpec.postcondition n result := by
  -- To prove the equivalence, we can split into cases based on the value of `result`.
  by_cases h_result : result <;> simp [LeetProofSpec.postcondition, VerinaSpec.isPrime_postcond];
  · -- If result is true, then the postcondition is that n is prime. This follows directly from the definition of the postcondition.
    apply Iff.intro;
    · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.prime_def_lt' ];
      · cases h_precond;
      · contradiction;
      · exact fun h m hm₁ hm₂ => fun hm₃ => h m hm₁ ( by linarith ) ( Nat.mod_eq_zero_of_dvd hm₃ );
    · -- If result is true and n is prime, then for any x between 2 and n-1, n%x is not zero.
      intro h_prime
      simp [h_prime, h_result];
      intro x hx₁ hx₂; rw [ ← Nat.dvd_iff_mod_eq_zero ] ; rw [ Nat.dvd_prime ( h_prime.mp h_result ) ] ; aesop;
  · rcases n with ( _ | _ | n ) <;> simp_all +arith +decide;
    · exact absurd h_precond ( by unfold VerinaSpec.isPrime_precond; decide );
    · exact absurd h_precond ( by unfold VerinaSpec.isPrime_precond; decide );
    · exact ⟨ fun ⟨ x, hx₁, hx₂ ⟩ => fun h => by have := Nat.dvd_of_mod_eq_zero hx₂; rw [ h.dvd_iff_eq ] at this <;> linarith, fun h => by obtain ⟨ x, hx₁, hx₂ ⟩ := Nat.exists_dvd_of_not_prime2 ( by linarith ) h; exact ⟨ x, ⟨ by linarith, by linarith ⟩, by simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ⟩ ⟩