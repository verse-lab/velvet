/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 38992187-cc64-47d1-85d9-846ee2c7e00a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Int):
  VerinaSpec.append_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Int) (result : Array Int) (h_precond : VerinaSpec.append_precond a b):
  VerinaSpec.append_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def append_precond (a : Array Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def copy (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copy a (i + 1) (acc.push (a[i]!))
  else
    acc

def append_postcond (a : Array Int) (b : Int) (result: Array Int) (h_precond : append_precond (a) (b)) :=
  -- !benchmark @start postcond
  (List.range' 0 a.size |>.all (fun i => result[i]! = a[i]!)) ∧
  result[a.size]! = b ∧
  result.size = a.size + 1

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No special preconditions needed
def precondition (a : Array Int) (b : Int) :=
  True

-- Postcondition: The result array has the correct size and elements
-- - The size is one more than the original array
-- - All original elements are preserved at their positions
-- - The new element is at the last position
def postcondition (a : Array Int) (b : Int) (result : Array Int) :=
  result.size = a.size + 1 ∧
  (∀ i : Nat, i < a.size → result[i]! = a[i]!) ∧
  result[a.size]! = b

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (b : Int):
  VerinaSpec.append_precond a b ↔ LeetProofSpec.precondition a b := by
  exact?

theorem postcondition_equiv (a : Array Int) (b : Int) (result : Array Int) (h_precond : VerinaSpec.append_precond a b):
  VerinaSpec.append_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  unfold VerinaSpec.append_postcond LeetProofSpec.postcondition; aesop;