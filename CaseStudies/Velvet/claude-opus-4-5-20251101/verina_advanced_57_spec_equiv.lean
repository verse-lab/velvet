/-
LeetProof's post-condition is incorrect

In the case where the result corresponds to the first greater
element after xPos, it requires that result[i] ≠ -1. However,
it is possible that the first greater element is actually -1,
in which case the postcondition would incorrectly reject a
valid result
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cda11ac7-134e-4f15-858f-ae06c0f1b4ec

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums1 : List Int) (nums2 : List Int):
  VerinaSpec.nextGreaterElement_precond nums1 nums2 ↔ LeetProofSpec.precondition nums1 nums2
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def nextGreaterElement_precond (nums1 : List Int) (nums2 : List Int) : Prop :=
  -- !benchmark @start precond
  List.Nodup nums1 ∧
  List.Nodup nums2 ∧
  nums1.all (fun x => x ∈ nums2)

-- !benchmark @end precond

@[reducible]
def nextGreaterElement_postcond (nums1 : List Int) (nums2 : List Int) (result: List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) : Prop :=
  -- !benchmark @start postcond
  result.length = nums1.length ∧

  (List.range nums1.length |>.all (fun i =>
    let val := nums1[i]!
    let resultVal := result[i]!

    let j := nums2.findIdx? (fun x => x == val)
    match j with
    | none => false
    | some idx =>
      let nextGreater := (List.range (nums2.length - idx - 1)).find? (fun k =>
        let pos := idx + k + 1
        nums2[pos]! > val
      )

      match nextGreater with
      | none => resultVal = -1
      | some offset => resultVal = nums2[idx + offset + 1]!
  )) ∧
  (result.all (fun val =>
    val = -1 ∨ val ∈ nums2
  ))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: check if all elements in list are unique
def allUnique (l : List Int) : Prop :=
  l.Nodup

-- Helper: check if list1 is a subset of list2
def isSubsetOf (l1 : List Int) (l2 : List Int) : Prop :=
  ∀ x, x ∈ l1 → x ∈ l2

-- Precondition clauses
def require1 (nums1 : List Int) (_nums2 : List Int) :=
  allUnique nums1

def require2 (_nums1 : List Int) (nums2 : List Int) :=
  allUnique nums2

def require3 (nums1 : List Int) (nums2 : List Int) :=
  isSubsetOf nums1 nums2

-- Postcondition clauses
-- The result has the same length as nums1
def ensures1 (nums1 : List Int) (_nums2 : List Int) (result : List Int) :=
  result.length = nums1.length

-- Property-based specification for next greater element
-- For each index i in result:
-- Case 1: result[i] = -1 means no element greater than nums1[i] exists after nums1[i]'s position in nums2
-- Case 2: result[i] ≠ -1 means result[i] is the first element greater than nums1[i] after its position in nums2
def ensures2 (nums1 : List Int) (nums2 : List Int) (result : List Int) :=
  ∀ i : Nat, i < nums1.length →
    let x := nums1[i]!
    let xPos := nums2.findIdx (· == x)
    -- Either result is -1 and no greater element exists after xPos
    (result[i]! = -1 ∧
     ∀ j : Nat, xPos < j → j < nums2.length → nums2[j]! ≤ x) ∨
    -- Or result is the first greater element after xPos
    (result[i]! ≠ -1 ∧
     ∃ k : Nat, xPos < k ∧ k < nums2.length ∧
          nums2[k]! = result[i]! ∧
          result[i]! > x ∧
          ∀ j : Nat, xPos < j → j < k → nums2[j]! ≤ x)

def precondition (nums1 : List Int) (nums2 : List Int) :=
  require1 nums1 nums2 ∧ require2 nums1 nums2 ∧ require3 nums1 nums2

def postcondition (nums1 : List Int) (nums2 : List Int) (result : List Int) :=
  ensures1 nums1 nums2 result ∧ ensures2 nums1 nums2 result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums1 : List Int) (nums2 : List Int):
  VerinaSpec.nextGreaterElement_precond nums1 nums2 ↔ LeetProofSpec.precondition nums1 nums2 := by
  constructor <;> intro h <;> unfold LeetProofSpec.precondition at * <;> aesop

theorem postcondition_equiv (nums1 : List Int) (nums2 : List Int) (result : List Int) (h_precond : VerinaSpec.nextGreaterElement_precond nums1 nums2):
  VerinaSpec.nextGreaterElement_postcond nums1 nums2 result h_precond ↔ LeetProofSpec.postcondition nums1 nums2 result := by
  constructor
  · intro h
    rcases h with ⟨hlen, hfind, hdomain⟩
    unfold LeetProofSpec.postcondition at *
    constructor
    · assumption
    · unfold LeetProofSpec.ensures2
      intro i hi num1i xpos
      rw [List.all_eq_true] at hfind
      specialize hfind i (by simp[hi])
      simp [hi] at hfind
      cases hidx : List.findIdx? (fun x ↦ x == nums1[i]) nums2 with
      | none => simp [hidx] at hfind
      | some ypos =>
          simp [hidx] at hfind
          simp [List.findIdx?_eq_some_iff_findIdx_eq] at *
          have hxy : xpos = ypos := by grind
          subst ypos
          cases hf : List.find? (fun k ↦ decide (nums1[i] < nums2[xpos + k + 1]?.getD 0)) (List.range (nums2.length - xpos - 1)) with
          | none =>
              simp [hf] at hfind
              left; constructor; assumption
              simp [List.find?_eq_none] at hf
              intros j hj1 hj2
              specialize hf (j - xpos - 1) (by grind)
              simp [num1i, hi];
              have hcalc : xpos + (j - xpos - 1) + 1 = j := by
                clear hf; grind
              simp [hcalc] at hf; assumption
          | some j =>
              simp [hf] at hfind
              simp [hlen, hi] at *
              rcases hf with ⟨hle, hj, hnear⟩
              have hle' : xpos + j + 1 < nums2.length := by grind
              simp [hle'] at *
              right; constructor
              · -- unprovable
                sorry
              sorry
  · sorry
