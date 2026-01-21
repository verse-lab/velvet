/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 39153ec7-03e0-4f38-8cda-c74030da4e54

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.majorityElement_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.majorityElement_precond nums):
  VerinaSpec.majorityElement_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic
import Std.Data.HashMap


open Std

namespace VerinaSpec

@[reducible]
def majorityElement_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  nums.length > 0 ∧ nums.any (fun x => nums.count x > nums.length / 2)

-- !benchmark @end precond

@[reducible]
def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length
  (nums.count result) > n / 2
  ∧ ∀ x ∈ nums, x ≠ result → nums.count x ≤ n / 2

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Check if an element is the majority element in a list
-- An element x is majority if it appears more than ⌊n/2⌋ times where n is the list length
def isMajority (nums : List Int) (x : Int) : Prop :=
  nums.count x > nums.length / 2

-- Precondition: list is non-empty and contains a majority element
def precondition (nums : List Int) :=
  nums.length ≥ 1 ∧ ∃ x, x ∈ nums ∧ isMajority nums x

-- Postcondition: result is in the list and is the majority element
def postcondition (nums : List Int) (result : Int) :=
  result ∈ nums ∧ isMajority nums result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.majorityElement_precond nums ↔ LeetProofSpec.precondition nums := by
  constructor <;> intro h <;> unfold LeetProofSpec.precondition at * <;> aesop

theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.majorityElement_precond nums):
  VerinaSpec.majorityElement_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  unfold VerinaSpec.majorityElement_postcond LeetProofSpec.postcondition;
  -- To prove the equivalence, we split the conjunction into two implications.
  apply Iff.intro;
  · -- If there's a majority element, then there must be some element in the list that appears more than half the time.
    have h_exists_majority : ∃ x ∈ nums, nums.count x > nums.length / 2 := by
      cases h_precond ; aesop;
    -- If there's a majority element, then there must be some element in the list that appears more than half the time. Hence, result must be in nums and be the majority element.
    intros h
    obtain ⟨x, hx₁, hx₂⟩ := h_exists_majority
    have hx₃ : result = x := by
      grind;
    unfold LeetProofSpec.isMajority; aesop;
  · -- By definition of majority element, we know that for any x in nums, if x ≠ result, then x cannot be the majority element.
    intros h
    have h_count : ∀ x ∈ nums, x ≠ result → ¬LeetProofSpec.isMajority nums x := by
      -- If x were a majority element, then the total number of elements would be at least (count of result) + (count of x) > n/2 + n/2 = n, which contradicts the fact that the total number of elements is n. Hence, x cannot be a majority element.
      intros x hx hx_ne_result
      by_contra hx_majority
      have h_total : (nums.count result) + (nums.count x) ≤ nums.length := by
        have h_total : ∀ {l : List ℤ}, (∀ x ∈ l, x = result ∨ x = x ∨ x ≠ result) → (l.count result) + (l.count x) ≤ l.length := by
          -- We can prove this by induction on the list.
          intro l hl
          induction' l with y l ih;
          · norm_num;
          · grind;
        exact h_total fun y hy => by tauto;
      unfold LeetProofSpec.isMajority at *; omega;
    -- By definition of count, if x is not the majority element, then its count is less than or equal to half the length of the list.
    have h_count_le : ∀ x ∈ nums, x ≠ result → List.count x nums ≤ nums.length / 2 := by
      exact fun x hx hx' => Nat.le_of_not_lt fun hx'' => h_count x hx hx' <| by unfold LeetProofSpec.isMajority; exact hx'';
    exact ⟨ h.2, h_count_le ⟩