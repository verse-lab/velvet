/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8d3c15b8-61f7-493f-a4f4-6dbdac6a53f8

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (key : Int):
  VerinaSpec.Find_precond a key ↔ LeetProofSpec.precondition a key

- theorem postcondition_equiv (a : Array Int) (key : Int) (result : Int) (h_precond : VerinaSpec.Find_precond a key):
  VerinaSpec.Find_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def Find_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def Find_postcond (a : Array Int) (key : Int) (result: Int) (h_precond : Find_precond (a) (key)) :=
  -- !benchmark @start postcond
  (result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
  ∧ ((result ≠ -1) → (a[(Int.toNat result)]! = key ∧ ∀ (i : Nat), i < Int.toNat result → a[i]! ≠ key))
  ∧ ((result = -1) → ∀ (i : Nat), i < a.size → a[i]! ≠ key)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input
def precondition (a : Array Int) (key : Int) : Prop :=
  True

-- Postcondition: Result is either -1 (not found) or the index of first occurrence
def postcondition (a : Array Int) (key : Int) (result : Int) : Prop :=
  -- Case 1: key not found - result is -1 and key does not appear in array
  (result = -1 ∧ ∀ i : Nat, i < a.size → a[i]! ≠ key) ∨
  -- Case 2: key found - result is valid index, element at result equals key,
  -- and all elements before result are not equal to key
  (result ≥ 0 ∧
   result < a.size ∧
   a[result.toNat]! = key ∧
   ∀ i : Nat, i < result.toNat → a[i]! ≠ key)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (key : Int):
  VerinaSpec.Find_precond a key ↔ LeetProofSpec.precondition a key := by
  -- Since both preconditions are defined as True, the equivalence is trivial.
  simp [VerinaSpec.Find_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Array Int) (key : Int) (result : Int) (h_precond : VerinaSpec.Find_precond a key):
  VerinaSpec.Find_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result := by
  have := @precondition_equiv a key;
  -- Since both postconditions are the same, the equivalence holds trivially.
  simp [VerinaSpec.Find_postcond, LeetProofSpec.postcondition];
  by_cases h : result = -1 <;> simp +decide [ h ];
  -- The conjunction of the conditions is equivalent to the individual conditions.
  simp [and_assoc, and_comm, and_left_comm]