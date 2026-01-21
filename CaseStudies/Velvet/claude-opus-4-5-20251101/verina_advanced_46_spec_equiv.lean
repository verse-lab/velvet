/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5e98cdd7-0747-4ff5-9218-5e6206c74331

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (numbers : List Int):
  VerinaSpec.maxSubarraySum_precond numbers ↔ LeetProofSpec.precondition numbers

- theorem postcondition_equiv (numbers : List Int) (result : Int) (h_precond : VerinaSpec.maxSubarraySum_precond numbers):
  VerinaSpec.maxSubarraySum_postcond numbers result h_precond ↔ LeetProofSpec.postcondition numbers result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def maxSubarraySum_precond (numbers : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def maxSubarraySum_postcond (numbers : List Int) (result: Int) (h_precond : maxSubarraySum_precond (numbers)) : Prop :=
  -- !benchmark @start postcond
  let subArraySums :=
    List.range (numbers.length + 1) |>.flatMap (fun start =>
      List.range (numbers.length - start + 1) |>.map (fun len =>
        numbers.drop start |>.take len |>.sum))
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function: sum of a contiguous subarray from index i to j (exclusive)
-- Uses List.take and List.drop to extract the subarray
def subarraySum (numbers : List Int) (i : Nat) (j : Nat) : Int :=
  ((numbers.drop i).take (j - i)).foldl (· + ·) 0

-- Property: a value is achievable as a contiguous subarray sum
-- This includes the empty subarray (when i = j, sum is 0)
def isAchievableSubarraySum (numbers : List Int) (val : Int) : Prop :=
  ∃ i j, i ≤ j ∧ j ≤ numbers.length ∧ subarraySum numbers i j = val

-- Property: a value is maximal among all contiguous subarray sums
def isMaximalSubarraySum (numbers : List Int) (val : Int) : Prop :=
  ∀ i j, i ≤ j → j ≤ numbers.length → subarraySum numbers i j ≤ val

-- Precondition: no restrictions on input
def precondition (numbers : List Int) : Prop :=
  True

-- Postcondition: result is the maximum contiguous subarray sum (with 0 as lower bound)
def postcondition (numbers : List Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  isAchievableSubarraySum numbers result ∧
  isMaximalSubarraySum numbers result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (numbers : List Int):
  VerinaSpec.maxSubarraySum_precond numbers ↔ LeetProofSpec.precondition numbers := by
  exact iff_of_true trivial trivial

theorem postcondition_equiv (numbers : List Int) (result : Int) (h_precond : VerinaSpec.maxSubarraySum_precond numbers):
  VerinaSpec.maxSubarraySum_postcond numbers result h_precond ↔ LeetProofSpec.postcondition numbers result := by
  constructor <;> intro h;
  · -- By definition of `maxSubarraySum_postcond`, we know that `result` is in the list of subarray sums and is the maximum.
    obtain ⟨h_result_in_list, h_max⟩ := h;
    refine' ⟨ _, _, _ ⟩;
    · simp_all +decide [ List.contains_iff_mem ];
      contrapose! h_max;
      exact ⟨ 0, by norm_num, 0, by norm_num, by simpa using h_max ⟩;
    · contrapose! h_result_in_list;
      simp_all +decide [ LeetProofSpec.isAchievableSubarraySum ];
      intro x hx y hy; specialize h_result_in_list x ( x + y ) ( by linarith ) ( by omega ) ; simp_all +decide [ LeetProofSpec.subarraySum ] ;
      convert h_result_in_list using 1;
      rw [ List.sum_eq_foldl ];
    · intro i j hij hj; simp_all +decide [ List.mem_flatMap ] ;
      convert h_max i ( by linarith ) ( j - i ) ( by omega ) using 1 ; simp +decide [ LeetProofSpec.subarraySum ] ; ring!;
      exact?;
  · -- By definition of `LeetProofSpec.isAchievableSubarraySum`, there exist indices `i` and `j` such that `i ≤ j`, `j ≤ numbers.length`, and `subarraySum numbers i j = result`.
    obtain ⟨i, j, hij, hsum⟩ := h.right.left;
    constructor;
    · simp +zetaDelta at *;
      exact ⟨ i, by linarith, j - i, by omega, by simpa [ List.sum_eq_foldl ] using hsum.2 ⟩;
    · simp +zetaDelta at *;
      intro x hx y hy; have := h.2.2 x ( x + y ) ( by linarith ) ( by omega ) ; simp_all +decide [ LeetProofSpec.subarraySum ] ;
      convert this using 1;
      exact?