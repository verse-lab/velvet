/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5afb9459-b1b1-44d5-90b7-31f82694c9c6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.isPalindrome_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.isPalindrome_precond s):
  VerinaSpec.isPalindrome_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isPalindrome_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def isPalindrome_postcond (s : String) (result: Bool) (h_precond : isPalindrome_precond (s)) : Prop :=
  -- !benchmark @start postcond
  (result → (s.toList == s.toList.reverse)) ∧
  (¬ result → (s.toList ≠ [] ∧ s.toList != s.toList.reverse))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions
-- Using Mathlib's List.reverse and String.toList

-- A string is a palindrome if its character list equals its reverse
def isPalindromeProperty (s : String) : Prop :=
  s.toList = s.toList.reverse

-- Postcondition: result is true iff the string is a palindrome
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ isPalindromeProperty s

def precondition (s : String) :=
  True

-- no preconditions

def postcondition (s : String) (result : Bool) :=
  ensures1 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.isPalindrome_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.isPalindrome_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.isPalindrome_precond s):
  VerinaSpec.isPalindrome_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  -- By definition of `isPalindrome_precond` and `precondition`, we know that both are always true.
  have h_precond_true : VerinaSpec.isPalindrome_precond s ∧ LeetProofSpec.precondition s := by
    -- Since both preconditions are always true, their conjunction is also true.
    simp [h_precond, LeetProofSpec.precondition];
  simp [VerinaSpec.isPalindrome_postcond, LeetProofSpec.postcondition, h_precond_true];
  cases result <;> simp_all +decide [ LeetProofSpec.ensures1 ];
  · unfold LeetProofSpec.isPalindromeProperty; aesop;
  · exact?