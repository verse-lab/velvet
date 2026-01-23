/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 71347389-9282-4c27-8f36-8d76b153cec2

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.reverse_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.reverse_precond a):
  VerinaSpec.reverse_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def reverse_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def reverse_core (arr : Array Int) (i : Nat) : Array Int :=
  if i < arr.size / 2 then
    let j := arr.size - 1 - i
    let temp := arr[i]!
    let arr' := arr.set! i (arr[j]!)
    let arr'' := arr'.set! j temp
    reverse_core arr'' (i + 1)
  else
    arr

def reverse_postcond (a : Array Int) (result: Array Int) (h_precond : reverse_precond (a)) :=
  -- !benchmark @start postcond
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → result[i]! = a[a.size - 1 - i]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input array
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: Result is the reverse of input array
-- 1. Same length as input
-- 2. For each index i, result[i] = a[size - 1 - i]
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ∀ i : Nat, i < a.size → result[i]! = a[a.size - 1 - i]!

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.reverse_precond a ↔ LeetProofSpec.precondition a := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.reverse_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.reverse_precond a):
  VerinaSpec.reverse_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  unfold VerinaSpec.reverse_postcond LeetProofSpec.postcondition; aesop;