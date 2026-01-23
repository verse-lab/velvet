/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a3c48ba2-5713-49f0-bbe0-4aaabcacb22a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.elementWiseModulo_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) (h_precond : VerinaSpec.elementWiseModulo_precond a b):
  VerinaSpec.elementWiseModulo_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def elementWiseModulo_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size ∧ a.size > 0 ∧
  (∀ i, i < b.size → b[i]! ≠ 0)

-- !benchmark @end precond

def elementWiseModulo_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :=
  -- !benchmark @start postcond
  result.size = a.size ∧
  (∀ i, i < result.size → result[i]! = a[i]! % b[i]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: arrays have same length and all elements in b are non-zero
def require1 (a : Array Int) (b : Array Int) :=
  a.size = b.size ∧ a.size > 0

def require2 (a : Array Int) (b : Array Int) :=
  ∀ i : Nat, i < b.size → b[i]! ≠ 0

-- Postcondition: result has same length as inputs
def ensures1 (a : Array Int) (b : Array Int) (result : Array Int) :=
  result.size = a.size

-- Postcondition: each element is the modulo of corresponding elements
def ensures2 (a : Array Int) (b : Array Int) (result : Array Int) :=
  ∀ i : Nat, i < a.size → result[i]! = a[i]! % b[i]!

def precondition (a : Array Int) (b : Array Int) :=
  require1 a b ∧ require2 a b

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) :=
  ensures1 a b result ∧ ensures2 a b result

end LeetProofSpec

theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.elementWiseModulo_precond a b ↔ LeetProofSpec.precondition a b := by
  -- To prove the equivalence of the preconditions, we show that they are equivalent definitions.
  simp [VerinaSpec.elementWiseModulo_precond, LeetProofSpec.precondition];
  -- By definition of `require1` and `require2`, we can split the conjunction into two implications.
  simp [LeetProofSpec.require1, LeetProofSpec.require2];
  -- The conjunction of three conditions is equivalent to the conjunction of two conditions.
  simp [and_assoc, and_comm, and_left_comm]

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) (h_precond : VerinaSpec.elementWiseModulo_precond a b):
  VerinaSpec.elementWiseModulo_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  -- By definition of VerinaSpec.elementWiseModulo_postcond and LeetProofSpec.postcondition, they are equivalent because they both check the same conditions: the result's size matches a's size and each element in the result is the modulo of the corresponding elements in a and b.
  simp [VerinaSpec.elementWiseModulo_postcond, LeetProofSpec.postcondition];
  unfold LeetProofSpec.ensures1 LeetProofSpec.ensures2; aesop;
