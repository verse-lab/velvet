/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: df58bfae-3162-4f6d-bd10-60278ebdab4e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : Array Nat):
  VerinaSpec.findSmallest_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : Array Nat) (result : Option Nat) (h_precond : VerinaSpec.findSmallest_precond s):
  VerinaSpec.findSmallest_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def findSmallest_precond (s : Array Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def findSmallest_postcond (s : Array Nat) (result: Option Nat) (h_precond : findSmallest_precond (s)) :=
  -- !benchmark @start postcond
  let xs := s.toList
  match result with
  | none => xs = []
  | some r => r ∈ xs ∧ (∀ x, x ∈ xs → r ≤ x)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper definition: check if a value is in the array
def inArrayNat (arr : Array Nat) (val : Nat) : Prop :=
  ∃ i : Nat, i < arr.size ∧ arr[i]! = val

-- Postcondition: characterizes the smallest element
def ensures1 (s : Array Nat) (result : Option Nat) :=
  match result with
  | none => s.size = 0
  | some x =>
      -- x is in the array
      inArrayNat s x ∧
      -- x is less than or equal to all elements in the array
      (∀ i : Nat, i < s.size → x ≤ s[i]!)

def precondition (s : Array Nat) :=
  True

-- no preconditions

def postcondition (s : Array Nat) (result : Option Nat) :=
  ensures1 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : Array Nat):
  VerinaSpec.findSmallest_precond s ↔ LeetProofSpec.precondition s := by
  -- By definition of `findSmallest_precond` and `precondition`, both are trivially true.
  simp [VerinaSpec.findSmallest_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (s : Array Nat) (result : Option Nat) (h_precond : VerinaSpec.findSmallest_precond s):
  VerinaSpec.findSmallest_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  unfold VerinaSpec.findSmallest_postcond LeetProofSpec.postcondition;
  unfold LeetProofSpec.ensures1;
  rcases result with ( _ | ⟨ r ⟩ ) <;> simp_all +decide [ List.mem_iff_get ];
  constructor <;> intro h;
  · exact ⟨ ⟨ _, h.1.choose.2, by simpa using h.1.choose_spec ⟩, fun i hi => h.2 ⟨ i, hi ⟩ ⟩;
  · -- From the hypothesis h, we know that r is in the array, so there exists some index i where s[i] = r.
    obtain ⟨i, hi⟩ : ∃ i : Fin s.size, s[i] = r := by
      rcases h.1 with ⟨ i, hi, hi' ⟩ ; exact ⟨ ⟨ i, hi ⟩, by simpa [ hi ] using hi' ⟩;
    exact ⟨ ⟨ i, hi ⟩, fun a => h.2 _ a.2 ⟩