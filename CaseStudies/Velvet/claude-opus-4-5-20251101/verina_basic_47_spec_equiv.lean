/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5e939488-f0a4-4ea0-a5d5-ee7d9e7f5363

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.arraySum_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.arraySum_precond a):
  VerinaSpec.arraySum_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def arraySum_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0

-- !benchmark @end precond

def sumTo (a : Array Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumTo a (n - 1) + a[n - 1]!

def arraySum_postcond (a : Array Int) (result: Int) (h_precond : arraySum_precond (a)) :=
  -- !benchmark @start postcond
  result - sumTo a a.size = 0 ∧
  result ≥ sumTo a a.size

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Using Array.sum from Mathlib/Init which computes sum via foldr (· + ·) 0

-- Precondition: array must be non-empty (based on reject inputs)
def precondition (a : Array Int) :=
  a.size > 0

-- Postcondition: result equals the sum of all array elements
-- Using index-based specification to describe the relationship
def postcondition (a : Array Int) (result : Int) :=
  result = a.toList.sum

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.arraySum_precond a ↔ LeetProofSpec.precondition a := by
  exact Iff.rfl

theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.arraySum_precond a):
  VerinaSpec.arraySum_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  unfold VerinaSpec.arraySum_postcond LeetProofSpec.postcondition;
  -- By definition of `sumTo`, we know that `sumTo a a.size` is the sum of all elements in `a`.
  have h_sumTo : VerinaSpec.sumTo a a.size = a.toList.sum := by
    -- By definition of `sumTo`, we know that `sumTo a n` is the sum of the first `n` elements of the list.
    have h_sumTo : ∀ n ≤ a.size, VerinaSpec.sumTo a n = List.sum (List.take n (a.toList)) := by
      intro n hn; induction' n with n ih <;> simp_all +decide [ List.take_succ ] ;
      · -- By definition of sumTo, when n is 0, it returns 0.
        simp [VerinaSpec.sumTo];
      · rw [ ← ih ( Nat.le_of_succ_le hn ), VerinaSpec.sumTo ];
        grind;
    rw [ h_sumTo _ le_rfl, List.take_of_length_le ( by simp +decide ) ];
  grind +ring