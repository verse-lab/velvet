/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6be2a2bd-f15b-4552-a7ca-8f63dafc5c81

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.semiOrderedPermutation_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.semiOrderedPermutation_precond nums):
  VerinaSpec.semiOrderedPermutation_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def semiOrderedPermutation_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  let n := nums.length
  n > 0 ∧
  -- Must be a permutation of [1..n]: all distinct, all in range
  List.Nodup nums ∧
  nums.all (fun x => 1 ≤ x ∧ x ≤ Int.ofNat n)

-- !benchmark @end precond

@[reducible]
def semiOrderedPermutation_postcond (nums : List Int) (result: Int) (h_precond : semiOrderedPermutation_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length
  let pos1 := nums.idxOf 1
  let posn := nums.idxOf (Int.ofNat n)
  if pos1 > posn then
    pos1 + n = result + 2 + posn
  else
    pos1 + n = result + 1 + posn

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if list contains all integers from 1 to n exactly once (valid permutation)
def isValidPermutation (nums : List Int) : Prop :=
  let n := nums.length
  n > 0 ∧
  (∀ x, x ∈ nums → 1 ≤ x ∧ x ≤ n) ∧
  nums.Nodup ∧
  (∀ k : Nat, 1 ≤ k ∧ k ≤ n → (k : Int) ∈ nums)

-- Helper: Find the index of an element in the list
def findIndex (nums : List Int) (val : Int) : Nat :=
  nums.findIdx (· == val)

-- Helper: Check if permutation is already semi-ordered
def isSemiOrdered (nums : List Int) : Prop :=
  nums.length > 0 ∧ nums[0]! = 1 ∧ nums[nums.length - 1]! = (nums.length : Int)

-- Helper: Perform one adjacent swap at position i (swap elements at i and i+1)
def swapAt (nums : List Int) (i : Nat) : List Int :=
  if i + 1 < nums.length then
    nums.set i (nums[i + 1]!) |>.set (i + 1) (nums[i]!)
  else
    nums

-- Precondition: nums must be a valid permutation of [1..n]
def precondition (nums : List Int) : Prop :=
  isValidPermutation nums

-- Postcondition: result is the minimum number of adjacent swaps to make permutation semi-ordered
-- Property-based specification using positions of 1 and n:
-- 1. Result is non-negative
-- 2. Result is 0 iff already semi-ordered
-- 3. Let idx1 = position of 1, idxN = position of n
--    - Distance for 1 to reach front = idx1
--    - Distance for n to reach end = (n - 1) - idxN  
--    - If idx1 > idxN, they cross during movement, saving 1 swap
-- 4. Result equals idx1 + ((n-1) - idxN) - (if idx1 > idxN then 1 else 0)
def postcondition (nums : List Int) (result : Int) : Prop :=
  let n := nums.length
  let idx1 := findIndex nums 1
  let idxN := findIndex nums (n : Int)
  -- Result is non-negative
  result ≥ 0 ∧
  -- Result is 0 iff already semi-ordered (1 at front, n at end)
  (result = 0 ↔ isSemiOrdered nums) ∧
  -- Position constraints: idx1 steps to move 1 to front, (n-1-idxN) steps to move n to end
  -- If 1 is to the right of n (idx1 > idxN), they cross, saving 1 swap
  (idx1 ≤ idxN → result = (idx1 : Int) + ((n - 1 : Int) - (idxN : Int))) ∧
  (idx1 > idxN → result = (idx1 : Int) + ((n - 1 : Int) - (idxN : Int)) - 1)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.semiOrderedPermutation_precond nums ↔ LeetProofSpec.precondition nums := by
  constructor;
  · -- If the list is a permutation of [1..n], then it satisfies the validity condition of the LeetProofSpec.precondition.
    intro h_precond
    obtain ⟨n, hn⟩ := h_precond;
    unfold LeetProofSpec.precondition;
    -- Since `nums` is a permutation of `[1, 2, ..., n]`, it contains all integers from 1 to n exactly once.
    have h_all : ∀ k : Nat, 1 ≤ k ∧ k ≤ nums.length → (k : ℤ) ∈ nums := by
      have h_perm : List.toFinset nums = Finset.Icc 1 (Int.ofNat nums.length) := by
        exact Finset.eq_of_subset_of_card_le ( fun x hx => by aesop ) ( by rw [ List.toFinset_card_of_nodup hn.1 ] ; aesop );
      intro k hk; replace h_perm := Finset.ext_iff.mp h_perm k; aesop;
    unfold LeetProofSpec.isValidPermutation; aesop;
  · unfold LeetProofSpec.precondition VerinaSpec.semiOrderedPermutation_precond;
    unfold LeetProofSpec.isValidPermutation; aesop;

noncomputable section AristotleLemmas

lemma precond_implies_mem (nums : List Int) (h : VerinaSpec.semiOrderedPermutation_precond nums) :
  1 ∈ nums ∧ (nums.length : Int) ∈ nums := by
    -- Since `nums` is a permutation of `[1..n]`, it contains all integers from 1 to `n` exactly once.
    have h_perm : nums.toFinset = Finset.Icc 1 (nums.length : ℤ) := by
      have h_perm : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ nums.length := by
        cases h ; aesop;
      refine' Finset.eq_of_subset_of_card_le ( fun x hx => by aesop ) _;
      rw [ List.toFinset_card_of_nodup ] <;> aesop;
    exact ⟨ List.mem_toFinset.mp ( h_perm.symm ▸ Finset.left_mem_Icc.mpr ( mod_cast h.1 ) ), List.mem_toFinset.mp ( h_perm.symm ▸ Finset.right_mem_Icc.mpr ( mod_cast h.1 ) ) ⟩

lemma result_arithmetic (n i j : Nat) (hn : n > 0) (hi : i < n) (hj : j < n) :
  let res := if i > j then (i : Int) + n - j - 2 else (i : Int) + n - j - 1
  res ≥ 0 ∧ (res = 0 ↔ i = 0 ∧ j = n - 1) := by
    grind

lemma isSemiOrdered_iff_indices (nums : List Int) (h : VerinaSpec.semiOrderedPermutation_precond nums) :
  LeetProofSpec.isSemiOrdered nums ↔ nums.idxOf 1 = 0 ∧ nums.idxOf (nums.length : Int) = nums.length - 1 := by
    constructor <;> intro h;
    · -- If the list is semi-ordered, then by definition, the first element is 1 and the last is n.
      obtain ⟨h_first, h_last⟩ := h;
      constructor;
      · cases nums <;> aesop;
      · -- Since `nums` is a permutation of `[1, 2, ..., n]`, `nums.length` is `n` and the last element is `n`.
        have h_last_element : ∀ i < nums.length, nums[i]! = nums.length → i = nums.length - 1 := by
          have h_last_element : List.Nodup nums := by
            exact h.2.1;
          intro i hi hi'; have := List.nodup_iff_injective_get.mp h_last_element; have := @this ⟨ i, hi ⟩ ⟨ List.length nums - 1, Nat.sub_lt h_first zero_lt_one ⟩ ; aesop;
        have h_last_element : List.idxOf (nums.length : ℤ) nums < nums.length := by
          grind;
        aesop;
    · unfold List.idxOf at h;
      -- Since `findIdx` returns the index of the first occurrence of an element, if `findIdx (fun x => x == 1) nums = 0`, then `nums[0]! = 1`.
      have h_first : nums[0]! = 1 := by
        grind;
      -- Since `findIdx` returns the index of the first occurrence of an element, if `findIdx (fun x => x == (nums.length : ℤ)) nums = nums.length - 1`, then `nums[nums.length - 1]! = (nums.length : ℤ)`.
      have h_last : nums[nums.length - 1]! = (nums.length : ℤ) := by
        grind;
      exact ⟨ by linarith [ ‹VerinaSpec.semiOrderedPermutation_precond nums›.1 ], h_first, h_last ⟩

end AristotleLemmas

theorem postcondition_equiv (nums : List Int) (result : Int) (h_precond : VerinaSpec.semiOrderedPermutation_precond nums):
  VerinaSpec.semiOrderedPermutation_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  -- Let's unfold the definition of `LeetProofSpec.postcondition`
  unfold LeetProofSpec.postcondition;
  -- By definition of `findIndex`, we know that `idx1 = pos1` and `idxN = posn`.
  have h_find_index : LeetProofSpec.findIndex nums 1 = List.idxOf 1 nums ∧ LeetProofSpec.findIndex nums (↑nums.length) = List.idxOf (↑nums.length) nums := by
    exact ⟨ rfl, rfl ⟩;
  have h_pos_bounds : List.idxOf 1 nums < nums.length ∧ List.idxOf (↑nums.length) nums < nums.length := by
    have h_pos_bounds : 1 ∈ nums ∧ (↑nums.length : ℤ) ∈ nums := by
      exact?;
    exact ⟨ by simpa using List.idxOf_lt_length_iff.mpr h_pos_bounds.1, by simpa using List.idxOf_lt_length_iff.mpr h_pos_bounds.2 ⟩;
  have h_is_semi_ordered : LeetProofSpec.isSemiOrdered nums ↔ List.idxOf 1 nums = 0 ∧ List.idxOf (↑nums.length) nums = nums.length - 1 := by
    apply isSemiOrdered_iff_indices;
    grind;
  grind