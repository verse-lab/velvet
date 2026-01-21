/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 23cf8521-e2b7-4265-aab8-67eeea8513ff

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.isSorted_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Bool) (h_precond : VerinaSpec.isSorted_precond a):
  VerinaSpec.isSorted_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isSorted_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def isSorted_postcond (a : Array Int) (result: Bool) (h_precond : isSorted_precond (a)) :=
  -- !benchmark @start postcond
  (∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]) ↔ result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Using Mathlib's Array.Pairwise to define sorted property
-- Array.Pairwise R as means all pairs (i, j) with i < j satisfy R as[i] as[j]

-- The sorted property: all pairs of elements with earlier index ≤ later index
def isSortedProp (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < a.size → j < a.size → i < j → a[i]! ≤ a[j]!

-- Precondition: No restrictions on input
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is true iff array is sorted in non-decreasing order
def postcondition (a : Array Int) (result : Bool) : Prop :=
  result = true ↔ isSortedProp a

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.isSorted_precond a ↔ LeetProofSpec.precondition a := by
  -- Since both preconditions are true, the equivalence holds trivially.
  simp [VerinaSpec.isSorted_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Bool) (h_precond : VerinaSpec.isSorted_precond a):
  VerinaSpec.isSorted_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- By definition of `VerinaSpec.isSorted_postcond`, we know that it is equivalent to `LeetProofSpec.postcondition`.
  simp [VerinaSpec.isSorted_postcond, LeetProofSpec.postcondition];
  -- The equivalence follows from the fact that the conditions are the same.
  apply Iff.intro;
  · -- If the original condition holds, then for any $i$ and $j$ with $i < j$, we have $a[i] \leq a[j]$.
    intro h
    apply Iff.intro;
    · intro h_true
      intro i j hi hj hij
      induction' hij with k hk ih;
      · grind;
      · grind;
    · unfold LeetProofSpec.isSortedProp; aesop;
  · -- If the result is true, then the array is sorted, which means that for all i < a.size - 1, a[i] ≤ a[i+1].
    intro h
    apply Iff.intro;
    · -- If the condition holds, then the array is sorted, which by h implies result is true.
      intro h_cond
      have h_sorted : LeetProofSpec.isSortedProp a := by
        intro i j hi hj hij;
        -- We can prove this by induction on $j - i$.
        induction' hij with m hm;
        · grind;
        · grind;
      aesop;
    · intro h_true i hi;
      have := h.mp h_true;
      specialize this i ( i + 1 ) ; aesop