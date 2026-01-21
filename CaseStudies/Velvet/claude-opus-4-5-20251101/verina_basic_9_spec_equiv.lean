/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8333ead5-47c0-44ed-9bd8-c4206626220e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.hasCommonElement_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Bool) (h_precond : VerinaSpec.hasCommonElement_precond a b):
  VerinaSpec.hasCommonElement_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def hasCommonElement_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ b.size > 0

-- !benchmark @end precond

def hasCommonElement_postcond (a : Array Int) (b : Array Int) (result: Bool) (h_precond : hasCommonElement_precond (a) (b)) :=
  -- !benchmark @start postcond
  (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Predicate: check if two arrays have at least one common element
def hasCommon (a : Array Int) (b : Array Int) : Prop :=
  ∃ x : Int, x ∈ a.toList ∧ x ∈ b.toList

-- Postcondition clauses
def ensures1 (a : Array Int) (b : Array Int) (result : Bool) :=
  result = true ↔ hasCommon a b

-- Precondition: both arrays must be non-empty
def precondition (a : Array Int) (b : Array Int) :=
  a.size > 0 ∧ b.size > 0

def postcondition (a : Array Int) (b : Array Int) (result : Bool) :=
  ensures1 a b result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.hasCommonElement_precond a b ↔ LeetProofSpec.precondition a b := by
  rfl

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Bool) (h_precond : VerinaSpec.hasCommonElement_precond a b):
  VerinaSpec.hasCommonElement_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  -- To prove the equivalence, we can use the fact that if there exist indices i and j such that a[i]! = b[j]!, then there exists an element x that is in both a.toList and b.toList, and vice versa. This is because the elements in the arrays are the same as the elements in their corresponding lists.
  have h_equiv : (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ ∃ x : Int, x ∈ a.toList ∧ x ∈ b.toList := by
    constructor <;> intro h;
    · obtain ⟨ i, j, hi, hj, h ⟩ := h;
      use a[i]!;
      grind;
    · obtain ⟨ x, hx₁, hx₂ ⟩ := h;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hx₁; obtain ⟨ j, hj ⟩ := List.mem_iff_get.1 hx₂; use i; use j; aesop;
  -- To prove the equivalence, we can use the fact that if there exist indices i and j such that a[i]! = b[j]!, then there exists an element x that is in both a.toList and b.toList, and vice versa. This is because the elements in the arrays are the same as the elements in their corresponding lists. Therefore, the postconditions are equivalent.
  simp [h_equiv, VerinaSpec.hasCommonElement_postcond, LeetProofSpec.postcondition];
  -- By definition of ensures1, we know that result = true ↔ hasCommon a b.
  simp [LeetProofSpec.ensures1];
  -- By definition of hasCommon, we know that result = true ↔ hasCommon a b.
  simp [LeetProofSpec.hasCommon];
  aesop