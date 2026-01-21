/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4bb58a49-1b0e-4894-9f71-9db9a30c95a4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.majorityElement_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.majorityElement_precond nums):
  VerinaSpec.majorityElement_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def majorityElement_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  nums.length > 0 ∧ nums.any (fun x => nums.count x > nums.length / 2)

-- majority element must exist
  -- !benchmark @end precond

def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length
  (List.count result nums > n / 2) ∧
  nums.all (fun x => x = result ∨ List.count x nums ≤ n / 2)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Check if an element is a majority element (appears more than n/2 times)
def isMajorityElement (nums : List Int) (x : Int) : Prop :=
  nums.count x > nums.length / 2

-- Check if a majority element exists in the list
def hasMajorityElement (nums : List Int) : Prop :=
  ∃ x ∈ nums, isMajorityElement nums x

-- Postcondition clauses

-- The result must be in the list
def ensures1 (nums : List Int) (result : Int) :=
  result ∈ nums

-- The result must appear more than n/2 times (majority element definition)
def ensures2 (nums : List Int) (result : Int) :=
  nums.count result > nums.length / 2

def precondition (nums : List Int) :=
  nums.length > 0 ∧ hasMajorityElement nums

def postcondition (nums : List Int) (result : Int) :=
  ensures1 nums result ∧ ensures2 nums result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.majorityElement_precond nums ↔ LeetProofSpec.precondition nums := by
  -- To prove the equivalence of the two preconditions, we can show that they both require the list to be non-empty and have a majority element.
  simp [VerinaSpec.majorityElement_precond, LeetProofSpec.precondition];
  aesop

theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.majorityElement_precond nums):
  VerinaSpec.majorityElement_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  -- By definition of `majorityElement_postcond`, we know that `result` is a majority element if and only if `result` is in the list and appears more than `n / 2` times.
  simp [VerinaSpec.majorityElement_postcond, LeetProofSpec.postcondition];
  constructor <;> intro h <;> simp_all +decide [ LeetProofSpec.ensures1, LeetProofSpec.ensures2 ];
  · -- Since the count of result is greater than zero, result must be present in the list.
    have h_count_pos : 0 < List.count result nums := by
      exact lt_of_le_of_lt ( Nat.zero_le _ ) h.1;
    exact?;
  · -- Since the sum of counts of all elements in the list is equal to the length of the list, and the count of result is more than n/2, the sum of counts of other elements must be less than n/2.
    have h_sum_counts : ∑ x ∈ nums.toFinset, List.count x nums = nums.length := by
      exact?;
    -- Since the sum of counts of all elements in the list is equal to the length of the list, and the count of result is more than n/2, the sum of counts of other elements must be less than n/2. Hence, for any x in the list, if x is not result, then List.count x nums ≤ nums.length / 2.
    intros x hx
    by_cases hx_result : x = result;
    · exact Or.inl hx_result;
    · have h_sum_counts_other : ∑ x ∈ nums.toFinset \ {result}, List.count x nums ≤ nums.length - List.count result nums := by
        rw [ ← h_sum_counts, ← Finset.sum_sdiff ( Finset.singleton_subset_iff.mpr ( show result ∈ nums.toFinset from by aesop ) ) ] ; aesop;
      have h_sum_counts_other : List.count x nums ≤ ∑ x ∈ nums.toFinset \ {result}, List.count x nums := by
        exact Finset.single_le_sum ( fun x _ => Nat.zero_le ( List.count x nums ) ) ( by aesop );
      omega