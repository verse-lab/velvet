/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 01e2ccad-128e-49cc-942a-efc1eda76e2d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Nat):
  VerinaSpec.missingNumber_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Nat) (result : Nat) (h_precond : VerinaSpec.missingNumber_precond nums):
  VerinaSpec.missingNumber_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def missingNumber_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums

-- !benchmark @end precond

@[reducible]
def missingNumber_postcond (nums : List Nat) (result: Nat) (h_precond : missingNumber_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length
  (result ∈ List.range (n + 1)) ∧
  ¬(result ∈ nums) ∧
  ∀ x, (x ∈ List.range (n + 1)) → x ≠ result → x ∈ nums

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper definition: all elements in list are distinct (no duplicates)
def allDistinct (nums : List Nat) : Prop :=
  nums.Nodup

-- Helper definition: all elements are within valid range [0, n]
def allInRange (nums : List Nat) (n : Nat) : Prop :=
  ∀ x, x ∈ nums → x ≤ n

-- Precondition: the list contains distinct elements all in range [0, n]
def precondition (nums : List Nat) :=
  allDistinct nums ∧ allInRange nums nums.length

-- Postcondition clauses
-- 1. The result is not in the list
def ensures1 (nums : List Nat) (result : Nat) :=
  result ∉ nums

-- 2. The result is in the valid range [0, n]
def ensures2 (nums : List Nat) (result : Nat) :=
  result ≤ nums.length

-- 3. Every other number in [0, n] is in the list (uniqueness)
def ensures3 (nums : List Nat) (result : Nat) :=
  ∀ k, k ≤ nums.length → k ≠ result → k ∈ nums

def postcondition (nums : List Nat) (result : Nat) :=
  ensures1 nums result ∧
  ensures2 nums result ∧
  ensures3 nums result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Nat):
  VerinaSpec.missingNumber_precond nums ↔ LeetProofSpec.precondition nums := by
  constructor <;> unfold VerinaSpec.missingNumber_precond LeetProofSpec.precondition <;> aesop

theorem postcondition_equiv (nums : List Nat) (result : Nat) (h_precond : VerinaSpec.missingNumber_precond nums):
  VerinaSpec.missingNumber_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  -- By definition of `missingNumber_postcond` and `postcondition`, we can show that they are equivalent by splitting the conjunction into its components and showing each component is equivalent.
  simp [VerinaSpec.missingNumber_postcond, LeetProofSpec.postcondition];
  -- By definition of `ensures1`, `ensures2`, and `ensures3`, we can split the conjunction into its components.
  simp [LeetProofSpec.ensures1, LeetProofSpec.ensures2, LeetProofSpec.ensures3];
  grind
