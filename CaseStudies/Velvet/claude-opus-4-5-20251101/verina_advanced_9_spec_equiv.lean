/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2cddb951-08d3-4e92-9219-9f8d62143b06

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat) (d : Nat):
  VerinaSpec.countSumDivisibleBy_precond n d ↔ LeetProofSpec.precondition n d

- theorem postcondition_equiv (n : Nat) (d : Nat) (result : Nat) (h_precond : VerinaSpec.countSumDivisibleBy_precond n d):
  VerinaSpec.countSumDivisibleBy_postcond n d result h_precond ↔ LeetProofSpec.postcondition n d result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def sumOfDigits (x : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + (n % 10))
  go x 0

@[reducible]
def countSumDivisibleBy_precond (n : Nat) (d : Nat) : Prop :=
  -- !benchmark @start precond
  d > 0

-- !benchmark @end precond

def isSumDivisibleBy (x : Nat) (d:Nat) : Bool :=
  (sumOfDigits x) % d = 0

@[reducible]
def countSumDivisibleBy_postcond (n : Nat) (d : Nat) (result: Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Prop :=
  -- !benchmark @start postcond
  (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n))) - result = 0 ∧
  result ≤ (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n)))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to compute the sum of digits of a natural number
-- This is a standard mathematical concept that requires recursion
def digitSum (n : Nat) : Nat :=
  if n < 10 then n
  else (n % 10) + digitSum (n / 10)

-- Precondition: d must be positive
def precondition (n : Nat) (d : Nat) : Prop :=
  d > 0

-- Postcondition: result equals the cardinality of the set of numbers in [0, n)
-- whose digit sum is divisible by d
-- Using Finset.filter and Finset.range for a property-based specification
def postcondition (n : Nat) (d : Nat) (result : Nat) : Prop :=
  result = (Finset.filter (fun k => d ∣ digitSum k) (Finset.range n)).card

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Nat) (d : Nat):
  VerinaSpec.countSumDivisibleBy_precond n d ↔ LeetProofSpec.precondition n d := by
  -- The preconditions are equivalent by definition.
  simp [VerinaSpec.countSumDivisibleBy_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (n : Nat) (d : Nat) (result : Nat) (h_precond : VerinaSpec.countSumDivisibleBy_precond n d):
  VerinaSpec.countSumDivisibleBy_postcond n d result h_precond ↔ LeetProofSpec.postcondition n d result := by
  unfold VerinaSpec.countSumDivisibleBy_postcond LeetProofSpec.postcondition;
  -- By definition of `VerinaSpec.sumOfDigits`, we know that `VerinaSpec.sumOfDigits x = LeetProofSpec.digitSum x`.
  have h_sum_eq : ∀ x, VerinaSpec.sumOfDigits x = LeetProofSpec.digitSum x := by
    -- By definition of `VerinaSpec.sumOfDigits.go`, we can prove this by induction on `n`.
    have h_ind : ∀ n acc, VerinaSpec.sumOfDigits.go n acc = acc + LeetProofSpec.digitSum n := by
      intro n acc; induction' n using Nat.strong_induction_on with n ih generalizing acc; rcases n with ( _ | _ | n ) <;> simp_all +arith +decide;
      · unfold VerinaSpec.sumOfDigits.go LeetProofSpec.digitSum; aesop;
      · unfold VerinaSpec.sumOfDigits.go LeetProofSpec.digitSum; simp +arith +decide;
        unfold VerinaSpec.sumOfDigits.go; aesop;
      · unfold VerinaSpec.sumOfDigits.go; simp +arith +decide [ ih ];
        rw [ ih _ ( Nat.div_le_of_le_mul <| by linarith ) ];
        unfold LeetProofSpec.digitSum; simp +arith +decide;
        split_ifs <;> try omega;
        · interval_cases _ : ( n + 2 ) / 10 <;> simp_all +decide;
          all_goals unfold LeetProofSpec.digitSum; simp +arith +decide;
        · rw [ show LeetProofSpec.digitSum ( ( n + 2 ) / 10 ) = LeetProofSpec.digitSum ( ( n + 2 ) / 10 / 10 ) + ( ( n + 2 ) / 10 ) % 10 from ?_ ];
          rw [ LeetProofSpec.digitSum ];
          grind;
    exact fun x => by simpa using h_ind x 0;
  -- The length of the filtered list is equal to the number of elements in the range n that satisfy the condition.
  have h_length_eq : (List.filter (fun x => x < n ∧ VerinaSpec.sumOfDigits x % d = 0) (List.range n)).length = Finset.card (Finset.filter (fun x => x < n ∧ VerinaSpec.sumOfDigits x % d = 0) (Finset.range n)) := by
    congr;
  simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
  rw [ show { x ∈ Finset.range n | x < n ∧ LeetProofSpec.digitSum x % d = 0 } = { x ∈ Finset.range n | LeetProofSpec.digitSum x % d = 0 } by ext; aesop ] ; omega;