/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: adc3dffc-ff3b-4ce1-97e5-cbb283d37492

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Int) (a : Array Int):
  VerinaSpec.isGreater_precond n a ↔ LeetProofSpec.precondition n a

- theorem postcondition_equiv (n : Int) (a : Array Int) (result : Bool) (h_precond : VerinaSpec.isGreater_precond n a):
  VerinaSpec.isGreater_postcond n a result h_precond ↔ LeetProofSpec.postcondition n a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isGreater_precond (n : Int) (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0

-- !benchmark @end precond

def isGreater_postcond (n : Int) (a : Array Int) (result: Bool) (h_precond : isGreater_precond (n) (a)) :=
  -- !benchmark @start postcond
  (∀ i, (hi : i < a.size) → n > a[i]) ↔ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: The array must be non-empty
def precondition (n : Int) (a : Array Int) :=
  a.size > 0

-- Postcondition: result is true iff n is strictly greater than all elements in the array
def postcondition (n : Int) (a : Array Int) (result : Bool) :=
  result = true ↔ ∀ i : Nat, i < a.size → a[i]! < n

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (n : Int) (a : Array Int):
  VerinaSpec.isGreater_precond n a ↔ LeetProofSpec.precondition n a := by
  exact?

theorem postcondition_equiv (n : Int) (a : Array Int) (result : Bool) (h_precond : VerinaSpec.isGreater_precond n a):
  VerinaSpec.isGreater_postcond n a result h_precond ↔ LeetProofSpec.postcondition n a result := by
  unfold VerinaSpec.isGreater_postcond LeetProofSpec.postcondition; aesop;