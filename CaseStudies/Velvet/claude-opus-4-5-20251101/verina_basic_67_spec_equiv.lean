/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d946b6b2-b40b-4074-866e-d4d4227ddc34

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : List Char):
  VerinaSpec.IsPalindrome_precond x ↔ LeetProofSpec.precondition x

- theorem postcondition_equiv (x : List Char) (result : Bool) (h_precond : VerinaSpec.IsPalindrome_precond x):
  VerinaSpec.IsPalindrome_postcond x result h_precond ↔ LeetProofSpec.postcondition x result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def IsPalindrome_precond (x : List Char) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def isPalindromeHelper (x : List Char) (i j : Nat) : Bool :=
  if i < j then
    match x[i]?, x[j]? with
    | some ci, some cj =>
      if ci ≠ cj then false else isPalindromeHelper x (i + 1) (j - 1)
    | _, _ => false  -- This case should not occur due to valid indices
  else true

def IsPalindrome_postcond (x : List Char) (result: Bool) (h_precond : IsPalindrome_precond (x)) :=
  -- !benchmark @start postcond
  result ↔ ∀ i : Nat, i < x.length → (x[i]! = x[x.length - i - 1]!)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions
-- Using Mathlib's List.reverse for reversing lists
-- Using the property: a list is a palindrome iff it equals its reverse

-- Postcondition clauses
-- The result is true if and only if the list equals its reverse
def ensures1 (x : List Char) (result : Bool) :=
  result = true ↔ x.reverse = x

def precondition (x : List Char) :=
  True

-- no preconditions, any list is valid input

def postcondition (x : List Char) (result : Bool) :=
  ensures1 x result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (x : List Char):
  VerinaSpec.IsPalindrome_precond x ↔ LeetProofSpec.precondition x := by
  -- Since both preconditions are True, the equivalence holds trivially.
  simp [VerinaSpec.IsPalindrome_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (x : List Char) (result : Bool) (h_precond : VerinaSpec.IsPalindrome_precond x):
  VerinaSpec.IsPalindrome_postcond x result h_precond ↔ LeetProofSpec.postcondition x result := by
  unfold VerinaSpec.IsPalindrome_postcond LeetProofSpec.postcondition;
  unfold LeetProofSpec.ensures1;
  congr! 2;
  constructor <;> intro h;
  · -- By definition of `List.reverse`, we need to show that for every index `i`, the element at `i` in `x.reverse` is equal to the element at `i` in `x`.
    ext i;
    grind;
  · grind