/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 030f810e-5a2c-4c6c-8e73-efce57aaf827

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.productExceptSelf_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : List Int) (h_precond : VerinaSpec.productExceptSelf_precond nums):
  VerinaSpec.productExceptSelf_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic

namespace VerinaSpec

@[reducible]
def productExceptSelf_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

-- Helper: Compute prefix products.
-- prefix[i] is the product of all elements in nums before index i.
def computepref (nums : List Int) : List Int :=
  nums.foldl (fun acc x => acc ++ [acc.getLast! * x]) [1]

-- Helper: Compute suffix products.
-- suffix[i] is the product of all elements in nums from index i (inclusive) to the end.
-- We reverse the list and fold, then reverse back.
def computeSuffix (nums : List Int) : List Int :=
  let revSuffix := nums.reverse.foldl (fun acc x => acc ++ [acc.getLast! * x]) [1]
  revSuffix.reverse

-- Specification Helper: Product of a list of Ints
-- Defined locally if not available/imported
def myprod : List Int → Int
  | [] => 1
  | x :: xs => x * myprod xs

@[reducible]
def productExceptSelf_postcond (nums : List Int) (result: List Int) (h_precond : productExceptSelf_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  nums.length = result.length ∧
  (List.range nums.length |>.all (fun i =>
    result[i]! = some (myprod ((List.take i nums)) * (myprod (List.drop (i+1) nums)))))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function: product of a list of integers using fold
def listProduct (lst : List Int) : Int :=
  lst.foldl (· * ·) 1

-- Precondition: no specific constraints, accept any list
def precondition (nums : List Int) :=
  True

-- Postcondition:
-- 1. Result has the same length as input
-- 2. For each index i, result[i] equals the product of prefix (elements before i) times suffix (elements after i)
def postcondition (nums : List Int) (result : List Int) :=
  result.length = nums.length ∧
  ∀ i : Nat, i < nums.length →
    result[i]! = listProduct (nums.take i) * listProduct (nums.drop (i + 1))

end LeetProofSpec

theorem precondition_equiv (nums : List Int):
  VerinaSpec.productExceptSelf_precond nums ↔ LeetProofSpec.precondition nums := by
  exact Iff.rfl

theorem postcondition_equiv (nums : List Int) (result : List Int) (h_precond : VerinaSpec.productExceptSelf_precond nums):
  VerinaSpec.productExceptSelf_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  -- By definition of `postcondition`, we need to show that the result of `productExceptSelf` satisfies the conditions given in both specifications.
  simp [VerinaSpec.productExceptSelf_postcond, LeetProofSpec.postcondition];
  -- By definition of `VerinaSpec.myprod`, we have `VerinaSpec.myprod xs = List.prod xs`.
  have h_myprod : ∀ (xs : List ℤ), VerinaSpec.myprod xs = List.prod xs := by
    intro xs
    induction' xs with x xs ih;
    · rfl;
    · simp [ih, VerinaSpec.myprod];
  simp +decide [ h_myprod, eq_comm, List.prod_eq_foldl ];
  exact fun _ => Iff.rfl
