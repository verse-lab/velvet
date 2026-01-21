/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 73285e14-ccf2-4aee-9c90-8137903ff420

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (l1 : List Nat) (l2 : List Nat):
  VerinaSpec.addTwoNumbers_precond l1 l2 ↔ LeetProofSpec.precondition l1 l2

- theorem postcondition_equiv (l1 : List Nat) (l2 : List Nat) (result : List Nat) (h_precond : VerinaSpec.addTwoNumbers_precond l1 l2):
  VerinaSpec.addTwoNumbers_postcond l1 l2 result h_precond ↔ LeetProofSpec.postcondition l1 l2 result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def listToNat : List Nat → Nat
| []       => 0
| d :: ds  => d + 10 * listToNat ds

@[reducible]
def addTwoNumbers_precond (l1 : List Nat) (l2 : List Nat) : Prop :=
  -- !benchmark @start precond
  l1.length > 0 ∧ l2.length > 0 ∧
  (∀ d ∈ l1, d < 10) ∧ (∀ d ∈ l2, d < 10) ∧
  (l1.getLast! ≠ 0 ∨ l1 = [0]) ∧
  (l2.getLast! ≠ 0 ∨ l2 = [0])

-- !benchmark @end precond

@[reducible]
def addTwoNumbers_postcond (l1 : List Nat) (l2 : List Nat) (result: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : Prop :=
  -- !benchmark @start postcond
  listToNat result = listToNat l1 + listToNat l2 ∧
  (∀ d ∈ result, d < 10) ∧
  -- No leading zeros unless the result is zero
  (result.getLast! ≠ 0 ∨ (l1 = [0] ∧ l2 = [0] ∧ result = [0]))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a list represents valid digits (each element is 0-9)
def validDigits (l : List Nat) : Prop :=
  ∀ i : Nat, i < l.length → l[i]! < 10

-- Helper: Check if a digit list has no leading zeros (in reverse representation,
-- this means the last element is non-zero, unless the list is [0])
def noLeadingZeros (l : List Nat) : Prop :=
  l = [0] ∨ (l ≠ [] ∧ l.getLast! ≠ 0)

-- Precondition: Both lists are non-empty, contain valid digits, and have no leading zeros
def precondition (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1.length > 0 ∧
  l2.length > 0 ∧
  validDigits l1 ∧
  validDigits l2 ∧
  noLeadingZeros l1 ∧
  noLeadingZeros l2

-- Postcondition: The result represents the sum of the two input numbers
-- Specified relationally: the numeric value of result equals the sum of input values,
-- and result is in canonical form (valid digits, no leading zeros)
def postcondition (l1 : List Nat) (l2 : List Nat) (result : List Nat) : Prop :=
  -- The result represents the correct sum
  Nat.ofDigits 10 result = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2 ∧
  -- The result contains valid digits
  validDigits result ∧
  -- The result has no leading zeros (canonical form)
  noLeadingZeros result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (l1 : List Nat) (l2 : List Nat):
  VerinaSpec.addTwoNumbers_precond l1 l2 ↔ LeetProofSpec.precondition l1 l2 := by
  unfold VerinaSpec.addTwoNumbers_precond LeetProofSpec.precondition;
  simp [LeetProofSpec.validDigits, LeetProofSpec.noLeadingZeros];
  intro h1 h2; constructor <;> intro h <;> simp_all +decide [ List.getLast? ] ;
  · grind;
  · exact ⟨ fun d hd => by obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hd; aesop, fun d hd => by obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hd; aesop, by tauto, by tauto ⟩

theorem postcondition_equiv (l1 : List Nat) (l2 : List Nat) (result : List Nat) (h_precond : VerinaSpec.addTwoNumbers_precond l1 l2):
  VerinaSpec.addTwoNumbers_postcond l1 l2 result h_precond ↔ LeetProofSpec.postcondition l1 l2 result := by
  unfold VerinaSpec.addTwoNumbers_postcond LeetProofSpec.postcondition;
  -- By definition of `listToNat` and `Nat.ofDigits`, we can show that they are equivalent.
  have h_equiv : ∀ (l : List ℕ), VerinaSpec.listToNat l = Nat.ofDigits 10 l := by
    intro l; induction l <;> simp +arith +decide [ *, Nat.ofDigits ] ;
    exact?;
  constructor <;> intro h;
  · unfold LeetProofSpec.validDigits LeetProofSpec.noLeadingZeros; aesop;
  · -- By definition of `LeetProofSpec.validDigits` and `LeetProofSpec.noLeadingZeros`, we can conclude that the result satisfies the postcondition.
    have h_valid_digits : ∀ d ∈ result, d < 10 := by
      intros d hd
      have h_valid_digit : d < 10 := by
        obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hd;
        have := h.2.1 i ; aesop
      exact h_valid_digit
    have h_no_leading_zeros : result.getLast! ≠ 0 ∨ l1 = [0] ∧ l2 = [0] ∧ result = [0] := by
      cases h.2.2 <;> simp_all +decide [ List.getLast? ];
      have h_zero : ∀ (l : List ℕ), Nat.ofDigits 10 l = 0 → l = List.replicate l.length 0 := by
        -- We can prove this by induction on the list.
        intro l hl
        induction' l with d l ih;
        · rfl;
        · norm_num [ Nat.ofDigits ] at hl;
          grind;
      grind;
    aesop