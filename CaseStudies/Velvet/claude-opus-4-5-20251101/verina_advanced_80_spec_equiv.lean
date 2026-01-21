/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b8b99591-39f4-4c45-ad84-2a51aaa4648e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : Array Int) (target : Int):
  VerinaSpec.twoSum_precond nums target ↔ LeetProofSpec.precondition nums target

- theorem postcondition_equiv (nums : Array Int) (target : Int) (result : Array Nat) (h_precond : VerinaSpec.twoSum_precond nums target):
  VerinaSpec.twoSum_postcond nums target result h_precond ↔ LeetProofSpec.postcondition nums target result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  -- The array must have at least 2 elements
  nums.size ≥ 2 ∧

  -- There exists exactly one pair of indices whose values sum to the target
  (List.range nums.size).any (fun i =>
    (List.range i).any (fun j => nums[i]! + nums[j]! = target)) ∧

  -- No other pair sums to the target (ensuring uniqueness of solution)
  ((List.range nums.size).flatMap (fun i =>
    (List.range i).filter (fun j => nums[i]! + nums[j]! = target))).length = 1

-- !benchmark @end precond

@[reducible]
def twoSum_postcond (nums : Array Int) (target : Int) (result: Array Nat) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  -- !benchmark @start postcond
  -- Result contains exactly 2 indices
  result.size = 2 ∧

  -- The indices are valid (within bounds of the nums array)
  result[0]! < nums.size ∧ result[1]! < nums.size ∧

  -- The indices are in ascending order (sorted)
  result[0]! < result[1]! ∧

  -- The values at these indices sum to the target
  nums[result[0]!]! + nums[result[1]!]! = target

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a pair of indices (i, j) forms a valid solution
def isValidPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target

-- Helper: Check if there exists exactly one valid pair (for precondition)
def hasUniqueSolution (nums : Array Int) (target : Int) : Prop :=
  ∃ i j, isValidPair nums target i j ∧
    (∀ i' j', isValidPair nums target i' j' → i' = i ∧ j' = j)

-- Precondition: array has at least 2 elements and exactly one solution exists
def precondition (nums : Array Int) (target : Int) :=
  nums.size ≥ 2 ∧ hasUniqueSolution nums target

-- Postcondition: result contains the two valid indices in sorted order
def postcondition (nums : Array Int) (target : Int) (result : Array Nat) :=
  result.size = 2 ∧
  result[0]! < result[1]! ∧
  result[1]! < nums.size ∧
  nums[result[0]!]! + nums[result[1]!]! = target

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : Array Int) (target : Int):
  VerinaSpec.twoSum_precond nums target ↔ LeetProofSpec.precondition nums target := by
  constructor <;> intro h;
  · -- From the hypothesis h, we can extract the existence of exactly one pair of indices (i, j) such that nums[i]! + nums[j]! = target.
    obtain ⟨i, j, hij, h_unique⟩ : ∃ i j, i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target ∧ ∀ i' j', i' < j' → j' < nums.size → nums[i']! + nums[j']! = target → i' = i ∧ j' = j := by
      obtain ⟨i, j, hij, h_unique⟩ : ∃ i j, i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target := by
        rcases h with ⟨h₁, h₂, h₃⟩;
        contrapose! h₃;
        grind;
      -- Since the list of pairs has length 1, there can't be any other pairs. So, we can use that to show uniqueness.
      have h_unique : ∀ i' j', i' < j' → j' < nums.size → nums[i']! + nums[j']! = target → (i', j') = (i, j) := by
        have h_unique : ∀ l : List (ℕ × ℕ), l.length = 1 → ∀ x ∈ l, ∀ y ∈ l, x = y := by
          intros l hl x hx y hy; rw [ List.length_eq_one_iff ] at hl; aesop;
        contrapose! h_unique;
        use List.flatMap (fun i => List.map (fun j => (j, i)) (List.filter (fun j => nums[i]! + nums[j]! = target) (List.range i))) (List.range nums.size);
        simp_all +decide [ List.length_flatMap ];
        refine' ⟨ _, _ ⟩;
        · convert h.2.2 using 1;
          induction ( List.range nums.size ) <;> aesop;
        · obtain ⟨ i', j', hij', hj', h, h' ⟩ := h_unique; use i, j, ⟨ by linarith, by linarith, by linarith ⟩, i', j', ⟨ by linarith, by linarith, by linarith ⟩ ; aesop;
      exact ⟨ i, j, hij, by tauto, by tauto, fun i' j' hij' hj' h => by simpa using h_unique i' j' hij' hj' h ⟩;
    -- From the hypothesis h, we know that the array has at least two elements, which is the first part of the precondition.
    have h_size : nums.size ≥ 2 := by
      grind;
    exact ⟨ h_size, ⟨ i, j, ⟨ hij, h_unique.1, h_unique.2.1 ⟩, fun i' j' h => h_unique.2.2 i' j' h.1 h.2.1 h.2.2 ⟩ ⟩;
  · obtain ⟨ h1, h2 ⟩ := h;
    obtain ⟨ i, j, ⟨ hij, hlt, hsum ⟩, hunique ⟩ := h2;
    refine' ⟨ h1, _, _ ⟩;
    · norm_num [ List.range_succ_eq_map ];
      exact ⟨ j, hlt, i, hij, by linarith ⟩;
    · -- Since there is exactly one pair (i, j) such that nums[i]! + nums[j]! = target, the flatMap will produce exactly one element.
      have h_singleton : ∀ i' j', i' < j' → j' < nums.size → nums[i']! + nums[j']! = target → i' = i ∧ j' = j := by
        exact fun i' j' hij' hlt' hsum' => hunique i' j' ⟨ hij', hlt', hsum' ⟩;
      have h_singleton : ∀ i' ∈ List.range nums.size, List.filter (fun j => nums[i']! + nums[j]! = target) (List.range i') = if i' = j then [i] else [] := by
        intros i' hi'
        by_cases hi'_eq_j : i' = j;
        · simp [hi'_eq_j];
          rw [ List.filter_eq_cons_iff.mpr ];
          use List.range i, List.drop (i + 1) (List.range j);
          norm_num +zetaDelta at *;
          refine' ⟨ _, _, _, _ ⟩;
          · refine' List.ext_get _ _ <;> norm_num;
            · omega;
            · intro n hn h₂; rw [ List.getElem_append ] ; norm_num;
              intro h; rw [ List.getElem_cons ] ; norm_num;
              split_ifs <;> omega;
          · grind;
          · grind;
          · intros a ha;
            rw [ List.mem_iff_get ] at ha;
            grind;
        · rw [ List.filter_eq_nil_iff.mpr ] ; aesop;
          grind;
      rw [ List.length_flatMap ];
      rw [ List.sum_map_eq_nsmul_single j ] <;> norm_num [ h_singleton ];
      · grind;
      · grind

theorem postcondition_equiv (nums : Array Int) (target : Int) (result : Array Nat) (h_precond : VerinaSpec.twoSum_precond nums target):
  VerinaSpec.twoSum_postcond nums target result h_precond ↔ LeetProofSpec.postcondition nums target result := by
  unfold VerinaSpec.twoSum_postcond LeetProofSpec.postcondition;
  -- By commutativity of conjunction, we can rearrange the terms in the conjunction.
  simp [and_comm, and_assoc, and_left_comm];
  -- By transitivity of inequalities, if $result[0]! < result[1]!$ and $result[1]! < nums.size$, then $result[0]! < nums.size$.
  intros h_size h_sum h_lt h_lt_size
  exact lt_trans h_lt h_lt_size
