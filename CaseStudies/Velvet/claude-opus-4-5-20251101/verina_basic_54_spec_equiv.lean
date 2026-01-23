/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7956dbad-3ba9-43a0-be19-086c3090872c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.CanyonSearch_precond a b ↔ LeetProofSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Nat) (h_precond : VerinaSpec.CanyonSearch_precond a b):
  VerinaSpec.CanyonSearch_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList

-- !benchmark @end precond

def canyonSearchAux (a : Array Int) (b : Array Int) (m n d : Nat) : Nat :=
  if m < a.size ∧ n < b.size then
    let diff : Nat := ((a[m]! - b[n]!).natAbs)
    let new_d := if diff < d then diff else d
    if a[m]! <= b[n]! then
      canyonSearchAux a b (m + 1) n new_d
    else
      canyonSearchAux a b m (n + 1) new_d
  else
    d
termination_by a.size + b.size - m - n

def CanyonSearch_postcond (a : Array Int) (b : Array Int) (result: Nat) (h_precond : CanyonSearch_precond (a) (b)) :=
  -- !benchmark @start postcond
  (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: compute absolute difference between two integers as a natural number
def absDiff (x : Int) (y : Int) : Nat := (x - y).natAbs

-- Helper: check if a value is achievable as a difference between some pair
def isAchievableDiff (a : Array Int) (b : Array Int) (val : Nat) : Prop :=
  ∃ i j, i < a.size ∧ j < b.size ∧ absDiff a[i]! b[j]! = val

-- Helper: check if a value is minimal among all pairwise differences
def isMinimalDiff (a : Array Int) (b : Array Int) (val : Nat) : Prop :=
  ∀ i j, i < a.size → j < b.size → val ≤ absDiff a[i]! b[j]!

-- Helper: check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ i j, i ≤ j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition clauses
def require1 (a : Array Int) (b : Array Int) :=
  a.size > 0

-- First array is non-empty

def require2 (a : Array Int) (b : Array Int) :=
  b.size > 0

-- Second array is non-empty

def require3 (a : Array Int) (b : Array Int) :=
  isSortedNonDecreasing a

-- First array is sorted

def require4 (a : Array Int) (b : Array Int) :=
  isSortedNonDecreasing b

-- Second array is sorted

-- Postcondition clauses
def ensures1 (a : Array Int) (b : Array Int) (result : Nat) :=
  isAchievableDiff a b result

-- Result is achievable

def ensures2 (a : Array Int) (b : Array Int) (result : Nat) :=
  isMinimalDiff a b result

-- Result is minimal

def precondition (a : Array Int) (b : Array Int) :=
  require1 a b ∧ require2 a b ∧ require3 a b ∧ require4 a b

def postcondition (a : Array Int) (b : Array Int) (result : Nat) :=
  ensures1 a b result ∧ ensures2 a b result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (b : Array Int):
  VerinaSpec.CanyonSearch_precond a b ↔ LeetProofSpec.precondition a b := by
  -- The conditions for `a` and `b` being non-empty and sorted in non-decreasing order are equivalent in both definitions.
  simp [VerinaSpec.CanyonSearch_precond, LeetProofSpec.precondition];
  simp [LeetProofSpec.require1, LeetProofSpec.require2, LeetProofSpec.require3, LeetProofSpec.require4];
  unfold LeetProofSpec.isSortedNonDecreasing;
  -- To prove the equivalence, we can use the fact that the pairwise condition on the list is equivalent to the pairwise condition on the array's elements.
  have h_pairwise_eq : ∀ (l : List ℤ), List.Pairwise (· ≤ ·) l ↔ ∀ i j, i ≤ j → j < l.length → l.get! i ≤ l.get! j := by
    intro l;
    constructor;
    · intro hl i j hij hj;
      rw [ List.pairwise_iff_get ] at hl;
      cases hij.lt_or_eq <;> simp_all +decide [ List.get! ];
      convert hl ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ ‹_› using 1;
      rw [ List.getElem?_eq_getElem ] ; aesop;
    · intro h;
      rw [ List.pairwise_iff_get ];
      intro i j hij; specialize h i j hij.le; aesop;
  cases a ; cases b ; aesop

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Nat) (h_precond : VerinaSpec.CanyonSearch_precond a b):
  VerinaSpec.CanyonSearch_postcond a b result h_precond ↔ LeetProofSpec.postcondition a b result := by
  unfold VerinaSpec.CanyonSearch_postcond LeetProofSpec.postcondition;
  -- The equivalence follows directly from the definitions of `any` and `all`.
  simp [LeetProofSpec.ensures1, LeetProofSpec.ensures2];
  unfold LeetProofSpec.isAchievableDiff LeetProofSpec.isMinimalDiff; aesop;