/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 572352c1-b8fb-444e-ac17-dd0910d36a92

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.hasOnlyOneDistinctElement_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Bool) (h_precond : VerinaSpec.hasOnlyOneDistinctElement_precond a):
  VerinaSpec.hasOnlyOneDistinctElement_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def hasOnlyOneDistinctElement_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0

-- !benchmark @end precond

def hasOnlyOneDistinctElement_postcond (a : Array Int) (result: Bool) (h_precond : hasOnlyOneDistinctElement_precond (a)) :=
  -- !benchmark @start postcond
  let l := a.toList
  (result → List.Pairwise (· = ·) l) ∧
  (¬ result → (l.any (fun x => x ≠ l[0]!)))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Predicate: all elements in the array are equal to each other
def allElementsEqual (a : Array Int) : Prop :=
  ∀ i j : Nat, i < a.size → j < a.size → a[i]! = a[j]!

-- Postcondition clauses
def ensures1 (a : Array Int) (result : Bool) :=
  result = true ↔ allElementsEqual a

def precondition (a : Array Int) :=
  a.size > 0

def postcondition (a : Array Int) (result : Bool) :=
  ensures1 a result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.hasOnlyOneDistinctElement_precond a ↔ LeetProofSpec.precondition a := by
  -- The definitions of the preconditions are identical, so the equivalence holds trivially.
  simp [VerinaSpec.hasOnlyOneDistinctElement_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Bool) (h_precond : VerinaSpec.hasOnlyOneDistinctElement_precond a):
  VerinaSpec.hasOnlyOneDistinctElement_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- By definition of `hasOnlyOneDistinctElement_postcond` and `postcondition`, we can split into cases based on the value of `result`.
  cases' result with hresult hresult;
  · -- By definition of `postcondition`, we know that `result = false ↔ ¬allElementsEqual a`.
    simp [LeetProofSpec.postcondition];
    -- By definition of `hasOnlyOneDistinctElement_postcond`, if `result` is false, then there exists at least one element in the array that is different from the first element.
    simp [VerinaSpec.hasOnlyOneDistinctElement_postcond, LeetProofSpec.ensures1];
    unfold LeetProofSpec.allElementsEqual;
    grind;
  · unfold VerinaSpec.hasOnlyOneDistinctElement_postcond LeetProofSpec.postcondition;
    -- If the list is pairwise equal, then all elements must be the same. Conversely, if all elements are the same, then the list is pairwise equal.
    simp [List.pairwise_iff_get];
    -- To prove the equivalence, we split it into two implications.
    apply Iff.intro;
    · -- By definition of `allElementsEqual`, if for all `i j : Fin a.size`, `i < j → a[i] = a[j]`, then `allElementsEqual a` holds.
      intro h
      have h_all : ∀ i j : Fin a.size, a[i] = a[j] := by
        exact fun i j => if hij : i < j then h i j hij else if hij' : j < i then h j i hij' ▸ rfl else by rw [ le_antisymm ( le_of_not_gt hij ) ( le_of_not_gt hij' ) ] ;
      -- By definition of `allElementsEqual`, if for all `i j : Fin a.size`, `a[i] = a[j]`, then `allElementsEqual a` holds.
      unfold LeetProofSpec.ensures1; simp [h_all];
      intro i j hi hj; specialize h_all ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; aesop;
    · -- By definition of ensures1, if ensures1 a true holds, then all elements of a are equal.
      intro h_all_equal
      obtain ⟨h_eq, h_ne⟩ := h_all_equal;
      exact fun i j hij => by simpa using h_eq rfl i j i.2 j.2;