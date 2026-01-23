/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 50f29391-9591-40a0-b7b8-b96c43554e9e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (operations : List Int):
  VerinaSpec.below_zero_precond operations ↔ LeetProofSpec.precondition operations

- theorem postcondition_equiv (operations : List Int) (result : (Array Int × Bool)) (h_precond : VerinaSpec.below_zero_precond operations):
  VerinaSpec.below_zero_postcond operations result h_precond ↔ LeetProofSpec.postcondition operations result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def below_zero_precond (operations : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList

def below_zero_postcond (operations : List Int) (result: (Array Int × Bool)) (h_precond : below_zero_precond (operations)) :=
  -- !benchmark @start postcond
  let s := result.1
  let result := result.2
  s.size = operations.length + 1 ∧
  s[0]? = some 0 ∧
  (List.range (s.size - 1)).all (fun i => s[i + 1]? = some (s[i]! + operations[i]!)) ∧
  ((result = true) → ((List.range (operations.length)).any (fun i => s[i + 1]! < 0))) ∧
  ((result = false) → s.all (· ≥ 0))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper to compute the sum of the first n elements of a list
def listPrefixSum (ops : List Int) (n : Nat) : Int :=
  (ops.take n).sum

-- Precondition: no constraints on the input list
def precondition (operations : List Int) : Prop :=
  True

-- Postcondition: specifies the properties of the output array and boolean
def postcondition (operations : List Int) (result : Array Int × Bool) : Prop :=
  let arr := result.1
  let hasNegative := result.2
  -- The array size is one more than the operations length
  arr.size = operations.length + 1 ∧
  -- The first element is 0
  arr[0]! = 0 ∧
  -- Each element at index i equals the sum of the first i operations
  (∀ i : Nat, i ≤ operations.length → arr[i]! = listPrefixSum operations i) ∧
  -- The boolean is true iff there exists an index i (1 ≤ i ≤ operations.length) 
  -- such that the partial sum at index i is negative
  (hasNegative = true ↔ ∃ i : Nat, 1 ≤ i ∧ i ≤ operations.length ∧ arr[i]! < 0)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (operations : List Int):
  VerinaSpec.below_zero_precond operations ↔ LeetProofSpec.precondition operations := by
  -- Since both preconditions are trivially true, their equivalence is immediate.
  simp [VerinaSpec.below_zero_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (operations : List Int) (result : (Array Int × Bool)) (h_precond : VerinaSpec.below_zero_precond operations):
  VerinaSpec.below_zero_postcond operations result h_precond ↔ LeetProofSpec.postcondition operations result := by
  constructor;
  · -- By definition of `VerinaSpec.below_zero_postcond`, we know that `s` is the array of partial sums and that it satisfies the conditions.
    intro h_verina
    obtain ⟨s, hs⟩ := h_verina;
    refine' ⟨ s, _, _, _ ⟩;
    · cases h : result.1 ; aesop;
    · -- We proceed by induction on $i$.
      intro i hi
      induction' i with i ih;
      · cases h : result.1 ; aesop;
      · -- Substitute the induction hypothesis into the equation from hs.
        have h_subst : result.1[i + 1]! = (result.1[i]! + operations[i]) := by
          grind;
        simp_all +decide [ LeetProofSpec.listPrefixSum ];
        rw [ List.sum_take_succ, ih ( Nat.le_of_succ_le hi ) ];
    · grind;
  · intro h;
    cases' h with h1 h2 h3 h4;
    refine' ⟨ _, _, _, _ ⟩;
    · exact h1;
    · grind;
    · -- By definition of `buildS`, we know that each element at index `i` is the sum of the first `i + 1` operations.
      have h_sum : ∀ i ≤ operations.length, result.1[i]! = (List.take i operations).sum := by
        aesop;
      -- By definition of `buildS`, we know that each element at index `i` is the sum of the first `i + 1` operations. Therefore, for any `i` in the range, `result.1[i + 1]!` is equal to `result.1[i]! + operations[i]!`.
      have h_diff : ∀ i < operations.length, result.1[i + 1]! = result.1[i]! + operations[i]! := by
        intro i hi; rw [ h_sum i hi.le, h_sum ( i + 1 ) ( by linarith ) ] ; simp +decide [ List.take_succ ] ;
        cases h : operations[i]? <;> aesop;
      simp_all +decide [ List.range_succ ];
    · constructor <;> intro h <;> simp_all +decide [ List.any_eq_true ];
      · rcases h2.2.2 with ⟨ i, hi₁, hi₂, hi₃ ⟩ ; use i - 1 ; rcases i <;> aesop;
      · -- By induction on the length of the operations list, we can show that all elements in the array are non-negative.
        have h_ind : ∀ i ≤ operations.length, 0 ≤ result.1[i]! := by
          intro i hi; cases i <;> aesop;
        rw [ Array.all_iff_forall ];
        grind