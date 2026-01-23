/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 08bb067e-c514-4b06-b330-c75bf2f59d06

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (e : Int):
  VerinaSpec.LinearSearch_precond a e ↔ LeetProofSpec.precondition a e

- theorem postcondition_equiv (a : Array Int) (e : Int) (result : Nat) (h_precond : VerinaSpec.LinearSearch_precond a e):
  VerinaSpec.LinearSearch_postcond a e result h_precond ↔ LeetProofSpec.postcondition a e result
-/

import Lean
import Mathlib.Tactic
import Mathlib


namespace VerinaSpec

def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  -- !benchmark @start postcond
  result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input
def precondition (a : Array Int) (e : Int) :=
  True

-- Postcondition clauses
-- ensures1: result is at most the size of the array
def ensures1 (a : Array Int) (e : Int) (result : Nat) :=
  result ≤ a.size

-- ensures2: if result < a.size, then the element at result equals the target
def ensures2 (a : Array Int) (e : Int) (result : Nat) :=
  result < a.size → a[result]! = e

-- ensures3: all elements before result are different from the target (first occurrence property)
def ensures3 (a : Array Int) (e : Int) (result : Nat) :=
  ∀ i : Nat, i < result → a[i]! ≠ e

-- ensures4: if result = a.size, then target is not in the array
def ensures4 (a : Array Int) (e : Int) (result : Nat) :=
  result = a.size → ∀ i : Nat, i < a.size → a[i]! ≠ e

def postcondition (a : Array Int) (e : Int) (result : Nat) :=
  ensures1 a e result ∧
  ensures2 a e result ∧
  ensures3 a e result ∧
  ensures4 a e result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (e : Int):
  VerinaSpec.LinearSearch_precond a e ↔ LeetProofSpec.precondition a e := by
  bound

theorem postcondition_equiv (a : Array Int) (e : Int) (result : Nat) (h_precond : VerinaSpec.LinearSearch_precond a e):
  VerinaSpec.LinearSearch_postcond a e result h_precond ↔ LeetProofSpec.postcondition a e result := by
  -- By definition of `LinearSearch_postcond` and `postcondition`, we can split the equivalence into the three parts.
  simp [VerinaSpec.LinearSearch_postcond, LeetProofSpec.postcondition];
  -- By definition of `ensures1`, `ensures2`, `ensures3`, and `ensures4`, we can split the conjunction into the three parts.
  simp [LeetProofSpec.ensures1, LeetProofSpec.ensures2, LeetProofSpec.ensures3, LeetProofSpec.ensures4];
  -- By definition of disjunction, we can split the implication into two cases: result = a.size and result < a.size.
  intro h_result_le_size
  constructor;
  · aesop;
  · -- If result is not equal to a.size, then by the first part of the hypothesis, a[result]! must be e. So in this case, the disjunction holds because the second part is true.
    intro h
    cases lt_or_eq_of_le h_result_le_size <;> aesop