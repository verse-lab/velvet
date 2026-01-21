/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9297d8a7-9cdf-44bc-9629-ab4a7e30704d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int):
  VerinaSpec.longestIncreasingStreak_precond nums ↔ LeetProofSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Nat) (h_precond : VerinaSpec.longestIncreasingStreak_precond nums):
  VerinaSpec.longestIncreasingStreak_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def longestIncreasingStreak_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def longestIncreasingStreak_postcond (nums : List Int) (result: Nat) (h_precond : longestIncreasingStreak_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  -- Case 1: Empty list means result = 0
  (nums = [] → result = 0) ∧

  -- Case 2: If result > 0, there exists a streak of exactly that length
  (result > 0 →
    (List.range (nums.length - result + 1) |>.any (fun start =>
      -- Check bounds are valid
      start + result ≤ nums.length ∧
      -- Check all consecutive pairs in this streak are increasing
      (List.range (result - 1) |>.all (fun i =>
        nums[start + i]! < nums[start + i + 1]!)) ∧
      -- Check this streak can't be extended left (if possible)
      (start = 0 ∨ nums[start - 1]! ≥ nums[start]!) ∧
      -- Check this streak can't be extended right (if possible)
      (start + result = nums.length ∨ nums[start + result - 1]! ≥ nums[start + result]!)))) ∧

  -- Case 3: No streak longer than result exists
  (List.range (nums.length - result) |>.all (fun start =>
    List.range result |>.any (fun i =>
      start + i + 1 ≥ nums.length ∨ nums[start + i]! ≥ nums[start + i + 1]!)))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a subarray from index start with given length is strictly increasing
def isStrictlyIncreasingSubarray (nums : List Int) (start : Nat) (len : Nat) : Prop :=
  start + len ≤ nums.length ∧
  len ≥ 1 ∧
  ∀ i : Nat, i + 1 < len → nums[start + i]! < nums[start + i + 1]!

-- Helper: Check if there exists a strictly increasing contiguous subarray of given length
def existsStrictlyIncreasingOfLength (nums : List Int) (len : Nat) : Prop :=
  ∃ start : Nat, isStrictlyIncreasingSubarray nums start len

-- Helper: No strictly increasing contiguous subarray exists with length greater than given value
def noLongerStrictlyIncreasing (nums : List Int) (maxLen : Nat) : Prop :=
  ∀ len : Nat, len > maxLen → ¬existsStrictlyIncreasingOfLength nums len

-- Precondition: No constraints on input
def precondition (nums : List Int) : Prop :=
  True

-- Postcondition: result is the length of the longest strictly increasing contiguous subarray
def postcondition (nums : List Int) (result : Nat) : Prop :=
  -- Empty list case
  (nums.length = 0 → result = 0) ∧
  -- Non-empty list case: result is at least 1
  (nums.length > 0 → result ≥ 1) ∧
  -- Result cannot exceed list length
  result ≤ nums.length ∧
  -- There exists a strictly increasing subarray of length result (if non-empty)
  (nums.length > 0 → existsStrictlyIncreasingOfLength nums result) ∧
  -- No longer strictly increasing subarray exists
  noLongerStrictlyIncreasing nums result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Int):
  VerinaSpec.longestIncreasingStreak_precond nums ↔ LeetProofSpec.precondition nums := by
  -- Since both preconditions are True, the equivalence holds trivially.
  simp [VerinaSpec.longestIncreasingStreak_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (nums : List Int) (result : Nat) (h_precond : VerinaSpec.longestIncreasingStreak_precond nums):
  VerinaSpec.longestIncreasingStreak_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  constructor;
  · -- By definition of `longestIncreasingStreak_postcond`, we know that if `longestIncreasingStreak_postcond nums result h_precond` holds, then `result` is the length of the longest strictly increasing contiguous subarray in `nums`.
    intro h_postcond
    obtain ⟨h_empty, h_exists, h_no_longer⟩ := h_postcond;
    rcases result with ( _ | result ) <;> simp_all +decide [ List.range_succ ];
    · -- If `nums` is empty, then the length of the longest strictly increasing contiguous subarray is indeed 0.
      by_cases h_empty : nums = [];
      · -- Since the list is empty, the length of the longest increasing subarray is 0.
        simp [h_empty, LeetProofSpec.postcondition];
        -- Since the list is empty, there are no subarrays, so the condition is vacuously true.
        simp [LeetProofSpec.noLongerStrictlyIncreasing];
        -- Since the list is empty, there are no elements to form a subarray, so the condition is vacuously true.
        simp [LeetProofSpec.existsStrictlyIncreasingOfLength];
        simp [LeetProofSpec.isStrictlyIncreasingSubarray];
        aesop;
      · exact absurd ( h_no_longer ( nums.length - 1 ) ) ( Nat.not_le_of_gt ( Nat.sub_lt ( List.length_pos_iff.mpr h_empty ) zero_lt_one ) );
    · refine' ⟨ _, _, _, _, _ ⟩;
      · aesop;
      · exact fun _ => Nat.succ_pos _;
      · grind;
      · rcases h_exists with ( ⟨ x, hx₁, hx₂, hx₃, hx₄, hx₅ ⟩ | ⟨ hx₁, hx₂, hx₃, hx₄ ⟩ );
        · intro h_pos
          use x;
          constructor <;> aesop;
        · intro h_pos
          use nums.length - (result + 1);
          refine' ⟨ _, _, _ ⟩ <;> aesop;
      · intro len hlen;
        rintro ⟨ start, hstart ⟩;
        -- By definition of `isStrictlyIncreasingSubarray`, we know that `start + len ≤ nums.length`.
        obtain ⟨hstart_len, hstart_inc⟩ := hstart;
        specialize h_no_longer start ; simp_all +decide [ Nat.sub_add_cancel ];
        grind;
  · -- To prove the forward direction, we need to show that if the LeetProofSpec postcondition holds, then the VerinaSpec postcondition also holds.
    intro h_post
    constructor;
    · cases h_post ; aesop;
    · constructor;
      · intro h_pos;
        rcases h_post with ⟨ h₁, h₂, h₃, h₄, h₅ ⟩;
        rcases h₄ ( Nat.pos_of_ne_zero ( by aesop ) ) with ⟨ start, hstart₁, hstart₂, hstart₃ ⟩;
        by_cases hstart₄ : start = 0 ∨ nums[start - 1]! ≥ nums[start]!;
        · by_cases hstart₅ : start + result = nums.length ∨ nums[start + result - 1]! ≥ nums[start + result]!;
          · rw [ List.any_eq_true ];
            use start;
            grind;
          · contrapose! h₅;
            simp_all +decide [ LeetProofSpec.noLongerStrictlyIncreasing ];
            use result + 1;
            refine' ⟨ Nat.lt_succ_self _, start, _, _, _ ⟩ <;> norm_num;
            · omega;
            · intro i hi; cases lt_or_eq_of_le ( Nat.succ_le_of_lt hi ) <;> aesop;
        · contrapose! h₅;
          simp_all +decide [ LeetProofSpec.noLongerStrictlyIncreasing ];
          use result + 1;
          refine' ⟨ Nat.lt_succ_self _, _ ⟩;
          use start - 1;
          -- To prove the subarray is strictly increasing, we need to show that for all i in the range 0 to result, the element at start - 1 + i is less than the element at start - 1 + i + 1.
          have h_subarray : ∀ i : ℕ, i < result → nums[start - 1 + i]! < nums[start - 1 + i + 1]! := by
            intro i hi;
            rcases i with ( _ | i ) <;> simp_all +decide [ Nat.succ_eq_add_one, add_assoc ];
            · cases start <;> aesop;
            · convert hstart₃ i hi using 1 <;> ring;
              · rw [ show 1 + ( start - 1 ) = start by omega ] ; ring;
              · rw [ show 2 + ( start - 1 ) + i = 1 + i + start by linarith [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr hstart₄.1 ) ] ];
          exact ⟨ by omega, by omega, fun i hi => h_subarray i ( by omega ) ⟩;
      · cases h_post;
        -- By definition of `noLongerStrictlyIncreasing`, if `result` is the length of the longest strictly increasing subarray, then there cannot be any strictly increasing subarray of length `result + 1`.
        have h_no_longer : ¬LeetProofSpec.existsStrictlyIncreasingOfLength nums (result + 1) := by
          aesop;
        contrapose! h_no_longer;
        norm_num +zetaDelta at *;
        obtain ⟨ x, hx₁, hx₂ ⟩ := h_no_longer;
        use x;
        constructor;
        · omega;
        · grind