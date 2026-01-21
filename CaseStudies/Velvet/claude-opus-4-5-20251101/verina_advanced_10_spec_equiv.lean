/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 724bb1aa-560d-416c-b86e-d269202cb03a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem precondition_equiv (n : Nat) (primes : List Nat):
  VerinaSpec.findExponents_precond n primes ↔ LeetProofSpec.precondition n primes

- theorem postcondition_equiv (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) (h_precond : VerinaSpec.findExponents_precond n primes):
  VerinaSpec.findExponents_postcond n primes result h_precond ↔ LeetProofSpec.postcondition n primes result

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

import Lean
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Defs


namespace VerinaSpec

@[reducible]
def findExponents_precond (n : Nat) (primes : List Nat) : Prop :=
  -- !benchmark @start precond
  n > 0 ∧
  primes.length > 0 ∧
  primes.all (fun p => Nat.Prime p) ∧
  List.Nodup primes

-- !benchmark @end precond

@[reducible]
def findExponents_postcond (n : Nat) (primes : List Nat) (result: List (Nat × Nat)) (h_precond : findExponents_precond (n) (primes)) : Prop :=
  -- !benchmark @start postcond
  (n = result.foldl (fun acc (p, e) => acc * p ^ e) 1) ∧
  result.all (fun (p, _) => p ∈ primes) ∧
  primes.all (fun p => result.any (fun pair => pair.1 = p))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: check if all elements in a list are prime
def allPrimes (primes : List Nat) : Prop :=
  ∀ p, p ∈ primes → Nat.Prime p

-- Helper: extract the first components of pairs
def firsts (pairs : List (Nat × Nat)) : List Nat :=
  pairs.map (fun ⟨p, _⟩ => p)

-- Helper: check if all prime factors of n are in the given list
def allPrimeFactorsIn (n : Nat) (primes : List Nat) : Prop :=
  ∀ p, Nat.Prime p → p ∣ n → p ∈ primes

-- Precondition: n is positive, primes is non-empty, all are prime, distinct, and n is fully factorizable
def precondition (n : Nat) (primes : List Nat) : Prop :=
  n > 0 ∧
  primes.length > 0 ∧
  allPrimes primes ∧
  primes.Nodup ∧
  allPrimeFactorsIn n primes

-- Postcondition:
-- 1. The result has the same length as the input primes list
-- 2. The primes in the result match the input primes in order
-- 3. For each pair (p, e) in result, e is the p-adic valuation of n
def postcondition (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) : Prop :=
  result.length = primes.length ∧
  firsts result = primes ∧
  (∀ i : Nat, i < result.length → (result[i]!.2 = Nat.factorization n (result[i]!.1)))

end LeetProofSpec

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
The preconditions are not equivalent because VerinaSpec does not require n to be fully factorizable by primes, whereas LeetProofSpec does. We show a counterexample with n=6 and primes=[2].
-/
theorem precondition_counterexample : ¬ (VerinaSpec.findExponents_precond 6 [2] ↔ LeetProofSpec.precondition 6 [2]) := by
  -- Let's choose n=6 and primes=[2] as a counterexample.
  simp [VerinaSpec.findExponents_precond, LeetProofSpec.precondition];
  norm_num [ LeetProofSpec.allPrimes, LeetProofSpec.allPrimeFactorsIn ];
  exists 3

end AristotleLemmas

/-
Equivalence theorems
-/
theorem precondition_equiv (n : Nat) (primes : List Nat):
  VerinaSpec.findExponents_precond n primes ↔ LeetProofSpec.precondition n primes := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider $n = 6$ and $primes = [2]$. We need to show that the preconditions are not equivalent.
  use 6, [2];
  -- We verify that 6 satisfies the conditions of `VerinaSpec.findExponents_precond`.
  simp [VerinaSpec.findExponents_precond];
  -- We verify that 2 is prime.
  norm_num [LeetProofSpec.precondition];
  -- Show that 6 is not fully factorizable by 2.
  simp [LeetProofSpec.allPrimeFactorsIn];
  -- Show that 3 is a prime factor of 6 that is not in the list [2].
  intro h_prime
  use 3
  norm_num

-/
-- Equivalence theorems

theorem precondition_equiv (n : Nat) (primes : List Nat):
  VerinaSpec.findExponents_precond n primes ↔ LeetProofSpec.precondition n primes := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) (h_precond : VerinaSpec.findExponents_precond n primes):
  VerinaSpec.findExponents_postcond n primes result h_precond ↔ LeetProofSpec.postcondition n primes result := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose specific values for n, primes, and result that satisfy the conditions.
  use 60, [3, 2, 5];
  -- Let's choose the result to be [(2, 2), (3, 1), (5, 1)].
  use [(2, 2), (3, 1), (5, 1)];
  -- Show that the chosen values satisfy the preconditions.
  simp +decide [VerinaSpec.findExponents_precond, VerinaSpec.findExponents_postcond, LeetProofSpec.postcondition]

-/
theorem postcondition_equiv (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) (h_precond : VerinaSpec.findExponents_precond n primes):
  VerinaSpec.findExponents_postcond n primes result h_precond ↔ LeetProofSpec.postcondition n primes result := by
  sorry