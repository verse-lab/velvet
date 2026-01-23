/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d362e28a-b0fd-4f0e-b9c8-3934c660441e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.findFirstOdd_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Option Nat) (h_precond : VerinaSpec.findFirstOdd_precond a):
  VerinaSpec.findFirstOdd_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0

def findFirstOdd_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0

-- !benchmark @end precond

def findFirstOdd_postcond (a : Array Int) (result: Option Nat) (h_precond : findFirstOdd_precond (a)) :=
  -- !benchmark @start postcond
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if an integer is odd
def isOddInt (n : Int) : Prop := n % 2 ≠ 0

-- Helper: Check if an integer is even
def isEvenInt (n : Int) : Prop := n % 2 = 0

-- Precondition: array must be non-empty
def precondition (a : Array Int) :=
  a.size > 0

-- Postcondition: characterizes the result
def postcondition (a : Array Int) (result : Option Nat) :=
  match result with
  | none =>
      -- No odd number exists in the array
      ∀ i : Nat, i < a.size → isEvenInt a[i]!
  | some idx =>
      -- idx is a valid index with an odd number
      idx < a.size ∧
      isOddInt a[idx]! ∧
      -- idx is the smallest such index (all elements before are even)
      (∀ j : Nat, j < idx → isEvenInt a[j]!)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.findFirstOdd_precond a ↔ LeetProofSpec.precondition a := by
  -- The preconditions are equivalent because they are the same condition.
  simp [VerinaSpec.findFirstOdd_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Option Nat) (h_precond : VerinaSpec.findFirstOdd_precond a):
  VerinaSpec.findFirstOdd_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- By definition of `findFirstOdd_postcond` and `LeetProofSpec.postcondition`, we can show that they are equivalent.
  simp [VerinaSpec.findFirstOdd_postcond, LeetProofSpec.postcondition];
  -- By definition of `isOdd` and `isEvenInt`, we can rewrite the postconditions to show their equivalence.
  simp [VerinaSpec.isOdd, LeetProofSpec.isEvenInt];
  -- The two match expressions are identical, so the equivalence holds trivially.
  cases result <;> simp [LeetProofSpec.isOddInt]