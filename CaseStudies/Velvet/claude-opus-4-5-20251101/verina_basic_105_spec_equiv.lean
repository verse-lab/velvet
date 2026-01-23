/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 33622704-ca0b-4470-b186-bf86e17a575b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.arrayProduct_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) (h_precond : VerinaSpec.arrayProduct_precond a b):
  VerinaSpec.arrayProduct_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def arrayProduct_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size

-- !benchmark @end precond

def loop (a b : Array Int) (len : Nat) : Nat → Array Int → Array Int
  | i, c =>
    if i < len then
      let a_val := if i < a.size then a[i]! else 0
      let b_val := if i < b.size then b[i]! else 0
      let new_c := Array.set! c i (a_val * b_val)
      loop a b len (i+1) new_c
    else c

def arrayProduct_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arrayProduct_precond (a) (b)) :=
  -- !benchmark @start postcond
  (result.size = a.size) ∧ (∀ i, i < a.size → a[i]! * b[i]! = result[i]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: arrays must have equal length
def require1 (a : Array Int) (b : Array Int) :=
  a.size = b.size

-- Postcondition clause 1: result has same size as input arrays
def ensures1 (a : Array Int) (b : Array Int) (result : Array Int) :=
  result.size = a.size

-- Postcondition clause 2: each element is the product of corresponding elements
def ensures2 (a : Array Int) (b : Array Int) (result : Array Int) :=
  ∀ i : Nat, i < a.size → result[i]! = a[i]! * b[i]!

def precondition (a : Array Int) (b : Array Int) :=
  require1 a b

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) :=
  ensures1 a b result ∧
  ensures2 a b result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.arrayProduct_precond a b ↔ LeetProofSpec.precondition a b := by
  rfl

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) (h_precond : VerinaSpec.arrayProduct_precond a b):
  VerinaSpec.arrayProduct_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  -- By definition of `arrayProduct_postcond` and `postcondition`, we can split the equivalence into two implications.
  simp [VerinaSpec.arrayProduct_postcond, LeetProofSpec.postcondition];
  -- By definition of `ensures1` and `ensures2`, we can split the equivalence into two implications.
  simp [LeetProofSpec.ensures1, LeetProofSpec.ensures2];
  -- The equality is symmetric, so the two statements are equivalent.
  intros h_size
  simp [eq_comm]