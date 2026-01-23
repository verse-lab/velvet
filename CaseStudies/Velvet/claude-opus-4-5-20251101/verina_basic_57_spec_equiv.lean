/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a2481c31-d852-4a9d-bb35-37ed56b5fccf

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (numbers : Array Int) (threshold : Int):
  VerinaSpec.CountLessThan_precond numbers threshold ↔ LeetProofSpec.precondition numbers threshold

- theorem postcondition_equiv (numbers : Array Int) (threshold : Int) (result : Nat) (h_precond : VerinaSpec.CountLessThan_precond numbers threshold):
  VerinaSpec.CountLessThan_postcond numbers threshold result h_precond ↔ LeetProofSpec.postcondition numbers threshold result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i < numbers.size then
      let new_acc := if numbers[i]! < threshold then acc + 1 else acc
      count (i + 1) new_acc
    else
      acc
  count 0 0

def CountLessThan_postcond (numbers : Array Int) (threshold : Int) (result: Nat) (h_precond : CountLessThan_precond (numbers) (threshold)) :=
  -- !benchmark @start postcond
  result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: No restrictions on input
def precondition (numbers : Array Int) (threshold : Int) :=
  True

-- Postcondition: result equals the count of elements less than threshold
-- Using Array.countP which counts elements satisfying a predicate
def postcondition (numbers : Array Int) (threshold : Int) (result : Nat) :=
  result = numbers.countP (· < threshold)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (numbers : Array Int) (threshold : Int):
  VerinaSpec.CountLessThan_precond numbers threshold ↔ LeetProofSpec.precondition numbers threshold := by
  -- Since both preconditions are True, they are trivially equivalent.
  simp [VerinaSpec.CountLessThan_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (numbers : Array Int) (threshold : Int) (result : Nat) (h_precond : VerinaSpec.CountLessThan_precond numbers threshold):
  VerinaSpec.CountLessThan_postcond numbers threshold result h_precond ↔ LeetProofSpec.postcondition numbers threshold result := by
  unfold LeetProofSpec.postcondition VerinaSpec.CountLessThan_postcond;
  rw [ Nat.sub_eq_zero_iff_le, Nat.sub_eq_zero_iff_le ];
  -- By definition of `foldl`, we can show that it is equivalent to `countP`.
  have h_foldl_countP : ∀ (numbers : Array ℤ) (threshold : ℤ), Array.foldl (fun (count : ℕ) (n : ℤ) => if n < threshold then count + 1 else count) 0 numbers = Array.countP (fun x => x < threshold) numbers := by
    -- We can prove this by induction on the array.
    intro numbers threshold
    induction' numbers with n numbers ih;
    induction n using List.reverseRecOn <;> aesop;
  rw [ h_foldl_countP, le_antisymm_iff ]