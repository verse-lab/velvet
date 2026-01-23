/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 349a7a69-94ee-43ed-abdb-c9b9ea553fb1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.concat_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) (h_precond : VerinaSpec.concat_precond a b):
  VerinaSpec.concat_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def concat_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : concat_precond (a) (b)) :=
  -- !benchmark @start postcond
  result.size = a.size + b.size
    ∧ (∀ k, k < a.size → result[k]! = a[k]!)
    ∧ (∀ k, k < b.size → result[k + a.size]! = b[k]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input arrays
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- Postcondition: Characterizes the concatenated array
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  -- Length property: result length is sum of input lengths
  result.size = a.size + b.size ∧
  -- First part: indices 0 to a.size - 1 match array a
  (∀ i : Nat, i < a.size → result[i]! = a[i]!) ∧
  -- Second part: indices a.size to a.size + b.size - 1 match array b
  (∀ j : Nat, j < b.size → result[a.size + j]! = b[j]!)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.concat_precond a b ↔ LeetProofSpec.precondition a b := by
  exact iff_of_true trivial trivial

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) (h_precond : VerinaSpec.concat_precond a b):
  VerinaSpec.concat_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  -- By definition of `VerinaSpec.concat_postcond` and `LeetProofSpec.postcondition`, we can split the goal into two implications. Each part of the conjunction in `VerinaSpec.concat_postcond` is equivalent to the corresponding part in `LeetProofSpec.postcondition`.
  simp [VerinaSpec.concat_postcond, LeetProofSpec.postcondition];
  grind