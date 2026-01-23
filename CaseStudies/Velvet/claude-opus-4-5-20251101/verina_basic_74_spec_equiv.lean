/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 70a9592f-a464-4616-a820-858a1266b1d7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.maxArray_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.maxArray_precond a):
  VerinaSpec.maxArray_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def maxArray_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0

-- !benchmark @end precond

def maxArray_aux (a : Array Int) (index : Nat) (current : Int) : Int :=
  if index < a.size then
    let new_current := if current > a[index]! then current else a[index]!
    maxArray_aux a (index + 1) new_current
  else
    current

def maxArray_postcond (a : Array Int) (result: Int) (h_precond : maxArray_precond (a)) :=
  -- !benchmark @start postcond
  (∀ (k : Nat), k < a.size → result >= a[k]!) ∧ (∃ (k : Nat), k < a.size ∧ result = a[k]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a value is in the array
def inArray (a : Array Int) (val : Int) : Prop :=
  ∃ i : Nat, i < a.size ∧ a[i]! = val

-- Helper: Check if a value is greater than or equal to all elements
def isMaximal (a : Array Int) (val : Int) : Prop :=
  ∀ i : Nat, i < a.size → a[i]! ≤ val

-- Precondition: Array must be non-empty
def precondition (a : Array Int) : Prop :=
  a.size ≥ 1

-- Postcondition: Result is the maximum element
-- 1. Result is greater than or equal to all elements (maximality)
-- 2. Result is an element of the array (achievability)
def postcondition (a : Array Int) (result : Int) : Prop :=
  isMaximal a result ∧ inArray a result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.maxArray_precond a ↔ LeetProofSpec.precondition a := by
  exact?

theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.maxArray_precond a):
  VerinaSpec.maxArray_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- The two postconditions are equivalent because they both require that the result is the maximum element in the array.
  simp [LeetProofSpec.postcondition, VerinaSpec.maxArray_postcond];
  -- The two postconditions are equivalent because they both require that the result is the maximum element in the array and that it is actually present in the array.
  simp [LeetProofSpec.isMaximal, LeetProofSpec.inArray];
  -- The equivalence follows from the fact that equality is symmetric.
  simp [eq_comm]