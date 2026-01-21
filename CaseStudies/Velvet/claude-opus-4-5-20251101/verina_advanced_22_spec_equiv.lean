/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1d5c1746-bcba-4a9d-93ee-e03368fd9264

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Int):
  VerinaSpec.isPeakValley_precond lst ↔ LeetProofSpec.precondition lst

- theorem postcondition_equiv (lst : List Int) (result : Bool) (h_precond : VerinaSpec.isPeakValley_precond lst):
  VerinaSpec.isPeakValley_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isPeakValley_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def isPeakValley_postcond (lst : List Int) (result: Bool) (h_precond : isPeakValley_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  let len := lst.length
  let validPeaks :=
    List.range len |>.filter (fun p =>
      1 ≤ p ∧ p < len - 1 ∧

      -- check strictly increasing before peak
      (List.range p).all (fun i =>
        lst[i]! < lst[i + 1]!
      ) ∧

      -- check strictly decreasing after peak
      (List.range (len - 1 - p)).all (fun i =>
        lst[p + i]! > lst[p + i + 1]!
      )
    )
  (validPeaks != [] → result) ∧
  (validPeaks.length = 0 → ¬ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a portion of a list is strictly increasing (from index i to j inclusive)
def isStrictlyIncreasingRange (lst : List Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < lst.length ∧ ∀ k : Nat, i ≤ k → k < j → lst[k]! < lst[k + 1]!

-- Helper: Check if a portion of a list is strictly decreasing (from index i to j inclusive)
def isStrictlyDecreasingRange (lst : List Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < lst.length ∧ ∀ k : Nat, i ≤ k → k < j → lst[k]! > lst[k + 1]!

-- Helper: Check if there exists a valid peak index
def hasPeakValleyStructure (lst : List Int) : Prop :=
  ∃ peakIdx : Nat, 
    peakIdx > 0 ∧ 
    peakIdx < lst.length - 1 ∧
    isStrictlyIncreasingRange lst 0 peakIdx ∧
    isStrictlyDecreasingRange lst peakIdx (lst.length - 1)

def precondition (lst : List Int) :=
  True

-- no preconditions

def postcondition (lst : List Int) (result : Bool) :=
  result = true ↔ hasPeakValleyStructure lst

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (lst : List Int):
  VerinaSpec.isPeakValley_precond lst ↔ LeetProofSpec.precondition lst := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.isPeakValley_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (lst : List Int) (result : Bool) (h_precond : VerinaSpec.isPeakValley_precond lst):
  VerinaSpec.isPeakValley_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result := by
  constructor <;> intro h;
  · cases result <;> simp_all +decide [ VerinaSpec.isPeakValley_postcond ];
    · unfold LeetProofSpec.postcondition;
      -- If there's no peak index, then the postcondition is false.
      by_contra h_contra;
      obtain ⟨ peakIdx, h_peakIdx₁, h_peakIdx₂, h_peakIdx₃, h_peakIdx₄ ⟩ := Classical.not_not.1 ( show ¬¬LeetProofSpec.hasPeakValleyStructure lst from by tauto );
      specialize h peakIdx ( by omega ) h_peakIdx₁ h_peakIdx₂;
      obtain ⟨ x, hx₁, hx₂ ⟩ := h ( fun x hx => by have := h_peakIdx₃.2.2 x ( by linarith ) ( by linarith ) ; aesop );
      exact hx₂.not_lt <| by have := h_peakIdx₄.2.2 ( peakIdx + x ) ( by omega ) ( by omega ) ; aesop;
    · obtain ⟨ x, hx₁, hx₂, hx₃, hx₄, hx₅ ⟩ := h;
      refine' iff_of_true ( by tauto ) _;
      constructor;
      refine' ⟨ hx₂, hx₃, _, _ ⟩;
      · constructor <;> aesop;
      · refine' ⟨ _, _, _ ⟩;
        · linarith;
        · omega;
        · intro k hk₁ hk₂; specialize hx₅ ( k - x ) ( by omega ) ; rw [ show k = x + ( k - x ) by omega ] ; aesop;
  · unfold VerinaSpec.isPeakValley_postcond;
    unfold LeetProofSpec.postcondition at h;
    by_cases h' : result = Bool.true <;> simp_all +decide [ LeetProofSpec.hasPeakValleyStructure ];
    · obtain ⟨ peakIdx, hpeakIdx₁, hpeakIdx₂, hpeakIdx₃, hpeakIdx₄ ⟩ := h;
      refine' ⟨ peakIdx, _, _, _, _, _ ⟩;
      · exact lt_of_lt_of_le hpeakIdx₂ ( Nat.pred_le _ );
      · linarith;
      · assumption;
      · unfold LeetProofSpec.isStrictlyIncreasingRange at hpeakIdx₃; aesop;
      · intro x hx; have := hpeakIdx₄.2.2 ( peakIdx + x ) ( by omega ) ( by omega ) ; aesop;
    · contrapose! h;
      -- By definition of `h`, we can extract such an `x` and use it to construct the required peak index.
      obtain ⟨x, hx₁, hx₂, hx₃, hx₄, hx₅⟩ := h;
      refine' ⟨ x, hx₂, hx₃, ⟨ _, _, _ ⟩, ⟨ _, _, _ ⟩ ⟩;
      any_goals omega;
      · aesop;
      · intro k hk₁ hk₂; specialize hx₅ ( k - x ) ( by omega ) ; simp_all +decide [ add_assoc, Nat.add_sub_of_le hk₁ ] ;