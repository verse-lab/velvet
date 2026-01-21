/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 12698954-d18e-4697-a32e-c1453f04630e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (sub : List Int) (main : List Int):
  VerinaSpec.isSublist_precond sub main ↔ LeetProofSpec.precondition sub main

- theorem postcondition_equiv (sub : List Int) (main : List Int) (result : Bool) (h_precond : VerinaSpec.isSublist_precond sub main):
  VerinaSpec.isSublist_postcond sub main result h_precond ↔ LeetProofSpec.postcondition sub main result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isSublist_precond (sub : List Int) (main : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def isSublist_postcond (sub : List Int) (main : List Int) (result: Bool) (h_precond : isSublist_precond (sub) (main)) :=
  -- !benchmark @start postcond
  (∃ i, i + sub.length ≤ main.length ∧ sub = (main.drop i).take sub.length) ↔ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Using the standard IsInfix relation from Lean/Mathlib
-- List.IsInfix l₁ l₂ (written l₁ <:+: l₂) means l₁ appears as a contiguous subsequence in l₂

-- Postcondition: result is true iff sub is an infix of main
def ensures1 (sub : List Int) (main : List Int) (result : Bool) :=
  result = true ↔ sub <:+: main

def precondition (sub : List Int) (main : List Int) :=
  True

-- no preconditions

def postcondition (sub : List Int) (main : List Int) (result : Bool) :=
  ensures1 sub main result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (sub : List Int) (main : List Int):
  VerinaSpec.isSublist_precond sub main ↔ LeetProofSpec.precondition sub main := by
  -- Since both preconditions are true, the equivalence is trivial.
  simp [VerinaSpec.isSublist_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (sub : List Int) (main : List Int) (result : Bool) (h_precond : VerinaSpec.isSublist_precond sub main):
  VerinaSpec.isSublist_postcond sub main result h_precond ↔ LeetProofSpec.postcondition sub main result := by
  -- By definition of `isInfix`, we know that `sub` is an infix of `main` if and only if there exists an index `i` such that `sub` is equal to the sublist of `main` starting at `i` and having the same length as `sub`.
  have h_infix : sub <:+: main ↔ ∃ i, i + sub.length ≤ main.length ∧ sub = (main.drop i).take sub.length := by
    constructor <;> intro h_sub;
    · obtain ⟨ i, hi ⟩ := h_sub;
      -- By definition of `IsInfix`, if there exists a t such that i ++ sub ++ t = main, then the length of i must be less than or equal to the length of main.
      obtain ⟨t, ht⟩ := hi;
      use i.length;
      aesop;
    · obtain ⟨ i, hi, hi' ⟩ := h_sub;
      use List.take i main;
      use List.drop (i + sub.length) main;
      rw [ hi', ← List.take_add ];
      rw [ ← hi', List.take_append_drop ];
  -- By combining the results from h_infix and the definitions of the postconditions, we can conclude the proof.
  simp [VerinaSpec.isSublist_postcond, LeetProofSpec.postcondition, h_infix];
  unfold LeetProofSpec.ensures1; aesop;