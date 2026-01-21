/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f5121512-0f29-4ecc-9dc2-a07bfabebd11

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.firstEvenOddDifference_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.firstEvenOddDifference_precond a):
  VerinaSpec.firstEvenOddDifference_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isEven (n : Int) : Bool :=
  n % 2 == 0

def isOdd (n : Int) : Bool :=
  n % 2 != 0

def firstEvenOddDifference_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 1 ∧
  (∃ x ∈ a, isEven x) ∧
  (∃ x ∈ a, isOdd x)

-- !benchmark @end precond

def firstEvenOddDifference_postcond (a : Array Int) (result: Int) (h_precond : firstEvenOddDifference_precond (a)) :=
  -- !benchmark @start postcond
  ∃ i j, i < a.size ∧ j < a.size ∧ isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]! ∧
    (∀ k, k < i → isOdd (a[k]!)) ∧ (∀ k, k < j → isEven (a[k]!))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if integer is even
def isEven (n : Int) : Prop := n % 2 = 0

-- Helper: Check if integer is odd
def isOdd (n : Int) : Prop := n % 2 ≠ 0

-- Helper: Check if index i contains the first even number in array
def isFirstEvenAt (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧
  isEven a[i]! ∧
  ∀ j : Nat, j < i → ¬isEven a[j]!

-- Helper: Check if index j contains the first odd number in array
def isFirstOddAt (a : Array Int) (j : Nat) : Prop :=
  j < a.size ∧
  isOdd a[j]! ∧
  ∀ k : Nat, k < j → ¬isOdd a[k]!

-- Precondition: array contains at least one even and one odd number
def require1 (a : Array Int) :=
  ∃ x ∈ a, isEven x

def require2 (a : Array Int) :=
  ∃ x ∈ a, isOdd x

-- Postcondition: result is the difference between first even and first odd
def ensures1 (a : Array Int) (result : Int) :=
  ∃ i j : Nat,
    isFirstEvenAt a i ∧
    isFirstOddAt a j ∧
    result = a[i]! - a[j]!

def precondition (a : Array Int) :=
  require1 a ∧ require2 a

def postcondition (a : Array Int) (result : Int) :=
  ensures1 a result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.firstEvenOddDifference_precond a ↔ LeetProofSpec.precondition a := by
  constructor <;> intro h;
  · rcases h with ⟨ h1, ⟨ x, hx, hx' ⟩, ⟨ y, hy, hy' ⟩ ⟩;
    constructor;
    · use x;
      unfold VerinaSpec.isEven at hx'; unfold LeetProofSpec.isEven; aesop;
    · use y;
      unfold VerinaSpec.isOdd at hy'; unfold LeetProofSpec.isOdd at *; aesop;
  · obtain ⟨ x, hx, hx' ⟩ := h.1;
    obtain ⟨ y, hy, hy' ⟩ := h.2;
    constructor;
    · contrapose! hx'; rcases a with ⟨ ⟨ l ⟩ ⟩ <;> aesop;
    · unfold LeetProofSpec.isEven at hx'; unfold LeetProofSpec.isOdd at hy'; unfold VerinaSpec.isEven at *; unfold VerinaSpec.isOdd at *; aesop;

theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.firstEvenOddDifference_precond a):
  VerinaSpec.firstEvenOddDifference_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- By definition of postcondition, we know that if there exist i and j such that the conditions hold, then both postconditions hold.
  apply Iff.intro;
  · -- If there exist indices i and j in the VerinaSpec postcondition, then those same indices satisfy the LeetProofSpec postcondition.
    intro h_postcond
    obtain ⟨i, j, hi, hj, h_even, h_odd, h_diff, h_first_even, h_first_odd⟩ := h_postcond;
    use i, j;
    -- By definition of `isFirstEvenAt` and `isFirstOddAt`, we can conclude that `i` is the first even index and `j` is the first odd index.
    simp [LeetProofSpec.isFirstEvenAt, LeetProofSpec.isFirstOddAt];
    unfold VerinaSpec.isEven VerinaSpec.isOdd LeetProofSpec.isEven LeetProofSpec.isOdd at * ; aesop;
  · rintro ⟨ i, j, hi, hj, hij ⟩;
    -- By definition of `LeetProofSpec.isFirstEvenAt` and `LeetProofSpec.isFirstOddAt`, we know that `i` and `j` are the first even and odd indices, respectively.
    obtain ⟨hi₁, hi₂⟩ := hi
    obtain ⟨hj₁, hj₂⟩ := hj;
    use i, j;
    simp_all +decide [ LeetProofSpec.isEven, LeetProofSpec.isOdd, VerinaSpec.isEven, VerinaSpec.isOdd ]