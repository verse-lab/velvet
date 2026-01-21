/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9a0f4a3d-4466-4319-8033-3f2803449d37

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.cubeElements_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.cubeElements_precond a):
  VerinaSpec.cubeElements_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def cubeElements_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def cubeElements_postcond (a : Array Int) (result: Array Int) (h_precond : cubeElements_precond (a)) :=
  -- !benchmark @start postcond
  (result.size = a.size) ∧
  (∀ i, i < a.size → result[i]! = a[i]! * a[i]! * a[i]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to compute the cube of an integer
def cube (x : Int) : Int := x * x * x

-- Precondition: no restrictions on input
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result has same length and each element is the cube of corresponding input
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ∀ i : Nat, i < a.size → result[i]! = cube a[i]!

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.cubeElements_precond a ↔ LeetProofSpec.precondition a := by
  exact Iff.rfl

theorem postcondition_equiv (a : Array Int) (result : Array Int) (h_precond : VerinaSpec.cubeElements_precond a):
  VerinaSpec.cubeElements_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- By definition of postcondition, we have that the size of the result array equals the size of the input array and each element of the result array is the cube of the corresponding element of the input array.
  simp [VerinaSpec.cubeElements_postcond, LeetProofSpec.postcondition];
  -- By definition of `cube`, we know that `cube a[i]! = a[i]! * a[i]! * a[i]!`.
  simp [LeetProofSpec.cube]