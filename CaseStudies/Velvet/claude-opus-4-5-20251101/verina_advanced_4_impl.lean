import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    LongestIncreasingSubsequence: Find the length of the longest strictly increasing subsequence
    Natural language breakdown:
    1. Given an array of integers, find the longest subsequence where each element is strictly less than the next
    2. A subsequence is obtained by deleting some (possibly zero) elements from the array without changing the order of remaining elements
    3. "Strictly increasing" means each element is strictly less than the following element (not ≤, but <)
    4. We return the length of this longest increasing subsequence
    5. Examples:
       - [5, 2, 8, 6, 3, 6, 9, 7] → LIS could be [2, 3, 6, 9] with length 4
       - [3, 1, 2, 1, 0] → LIS could be [1, 2] with length 2
       - [] → Empty array has LIS of length 0
    6. Key properties:
       - A subsequence preserves relative order from the original array
       - The result is the maximum length over all possible strictly increasing subsequences
       - For empty array, result is 0
       - For any non-empty array, result is at least 1 (single element is trivially increasing)
-/

section Specs
-- Check if a list is strictly increasing using Mathlib's List.Chain'
-- This avoids explicit recursion
def isStrictlyIncreasing (sub : List Int) : Prop :=
  List.Chain' (· < ·) sub

-- Check if one list is a subsequence of another (preserves order, allows gaps)
-- Using Mathlib's List.Sublist
def isIncreasingSubseqOf (sub : List Int) (arr : Array Int) : Prop :=
  sub.Sublist arr.toList ∧ isStrictlyIncreasing sub

-- Precondition: no restrictions on input array
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is the length of the longest increasing subsequence
-- 1. Result is non-negative
-- 2. There exists an increasing subsequence of that length
-- 3. No increasing subsequence has length greater than result
def postcondition (a : Array Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ sub : List Int, isIncreasingSubseqOf sub a ∧ sub.length = result.toNat) ∧
  (∀ sub : List Int, isIncreasingSubseqOf sub a → sub.length ≤ result.toNat)
end Specs

section Impl
method LongestIncreasingSubsequence (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  if a.size = 0 then
    return 0
  else
    -- dp[i] = length of LIS ending at index i
    let mut dp := Array.replicate a.size 1
    let mut maxLen := 1
    
    -- For each position i, find the longest increasing subsequence ending at i
    let mut i := 1
    while i < a.size
      -- Invariant: i is within valid bounds
      invariant "i_bounds" 1 ≤ i ∧ i ≤ a.size
      -- Invariant: dp array maintains its size
      invariant "dp_size" dp.size = a.size
      -- Invariant: maxLen is at least 1
      invariant "maxLen_pos" maxLen ≥ 1
      -- Invariant: all dp values are at least 1
      invariant "dp_values_pos" ∀ k, k < a.size → dp[k]! ≥ 1
      -- Invariant: maxLen is the max of dp[0..i)
      invariant "maxLen_is_max" ∀ k, k < i → dp[k]! ≤ maxLen
      -- Invariant: there exists some index with dp value = maxLen
      invariant "maxLen_achieved" ∃ k, k < i ∧ dp[k]! = maxLen
      done_with i = a.size
    do
      let mut j := 0
      while j < i
        -- Invariant: j is within valid bounds
        invariant "j_bounds" 0 ≤ j ∧ j ≤ i
        -- Invariant: dp array maintains its size
        invariant "inner_dp_size" dp.size = a.size
        -- Invariant: current dp[i] is at least 1
        invariant "dp_i_pos" dp[i]! ≥ 1
        -- Invariant: all dp values remain at least 1
        invariant "inner_dp_values_pos" ∀ k, k < a.size → dp[k]! ≥ 1
        -- Invariant: maxLen bounds still hold for previous indices
        invariant "inner_maxLen_bound" ∀ k, k < i → dp[k]! ≤ maxLen
        -- Invariant: maxLen still achieved
        invariant "inner_maxLen_achieved" ∃ k, k < i ∧ dp[k]! = maxLen
        -- Invariant: i is still valid
        invariant "inner_i_bound" i < a.size
        -- Invariant: maxLen still positive
        invariant "inner_maxLen_pos" maxLen ≥ 1
        done_with j = i
      do
        -- If a[j] < a[i], we can extend the LIS ending at j
        if a[j]! < a[i]! then
          if dp[j]! + 1 > dp[i]! then
            dp := dp.set! i (dp[j]! + 1)
        j := j + 1
      
      -- Update the global maximum
      if dp[i]! > maxLen then
        maxLen := dp[i]!
      
      i := i + 1
    
    return maxLen
end Impl

section TestCases
-- Test case 1: Example from problem - mixed array with LIS of length 4
def test1_a : Array Int := #[5, 2, 8, 6, 3, 6, 9, 7]
def test1_Expected : Int := 4

-- Test case 2: Decreasing-ish array with small LIS
def test2_a : Array Int := #[3, 1, 2, 1, 0]
def test2_Expected : Int := 2

-- Test case 3: Longer array with LIS of length 6
def test3_a : Array Int := #[2, 3, -2, -1, 7, 19, 3, 6, -4, 6, -7, 0, 9, 12, 10]
def test3_Expected : Int := 6

-- Test case 4: Mixed array with negative numbers
def test4_a : Array Int := #[5, -5, -3, 2, 4, 1, 0, -1, 3, 2, 0]
def test4_Expected : Int := 4

-- Test case 5: Array with various patterns
def test5_a : Array Int := #[1, 7, 23, 14, -4, 21, 8, 2, -1, 9, 12, 2]
def test5_Expected : Int := 5

-- Test case 6: Empty array - edge case
def test6_a : Array Int := #[]
def test6_Expected : Int := 0

-- Test case 7: Single element array
def test7_a : Array Int := #[42]
def test7_Expected : Int := 1

-- Test case 8: Already sorted increasing array
def test8_a : Array Int := #[1, 2, 3, 4, 5]
def test8_Expected : Int := 5

-- Test case 9: All same elements
def test9_a : Array Int := #[5, 5, 5, 5]
def test9_Expected : Int := 1

-- Test case 10: Strictly decreasing array
def test10_a : Array Int := #[5, 4, 3, 2, 1]
def test10_Expected : Int := 1

-- Recommend to validate: 1, 6, 8
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((LongestIncreasingSubsequence test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((LongestIncreasingSubsequence test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((LongestIncreasingSubsequence test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((LongestIncreasingSubsequence test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((LongestIncreasingSubsequence test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((LongestIncreasingSubsequence test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((LongestIncreasingSubsequence test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((LongestIncreasingSubsequence test8_a).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((LongestIncreasingSubsequence test9_a).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((LongestIncreasingSubsequence test10_a).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 182, Column 0
-- Message: unsolved goals
-- case refine_2.refine_1
-- a : Array ℤ
-- result : ℤ
-- ⊢ Decidable (∃ sub, isIncreasingSubseqOf sub a ∧ sub.length = result.toNat)
-- 
-- case refine_2.refine_2
-- a : Array ℤ
-- result : ℤ
-- ⊢ Decidable (∀ (sub : List ℤ), isIncreasingSubseqOf sub a → sub.length ≤ result.toNat)
-- Line: prove_postcondition_decidable_for LongestIncreasingSubsequence
-- [ERROR] Line 184, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for LongestIncreasingSubsequence
-- prove_precondition_decidable_for LongestIncreasingSubsequence
-- prove_postcondition_decidable_for LongestIncreasingSubsequence
-- derive_tester_for LongestIncreasingSubsequence
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
--     let res := LongestIncreasingSubsequenceTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct LongestIncreasingSubsequence by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_1_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (dp : Array ℕ)
    (i : ℕ)
    (maxLen : ℕ)
    (a_1 : 1 ≤ i)
    (a_2 : i ≤ a.size)
    (invariant_dp_size : dp.size = a.size)
    (invariant_maxLen_is_max : ∀ k < i, dp[k]! ≤ maxLen)
    (invariant_maxLen_achieved : ∃ k < i, dp[k]! = maxLen)
    (if_pos : i < a.size)
    (dp_1 : Array ℕ)
    (j : ℕ)
    (a_4 : j ≤ i)
    (invariant_inner_dp_size : dp_1.size = a.size)
    (invariant_inner_maxLen_bound : ∀ k < i, dp_1[k]! ≤ maxLen)
    (invariant_inner_maxLen_achieved : ∃ k < i, dp_1[k]! = maxLen)
    (invariant_inner_i_bound : i < a.size)
    (if_pos_1 : j < i)
    (if_pos_2 : a[j]! < a[i]!)
    (if_neg : ¬a = #[])
    (invariant_maxLen_pos : 1 ≤ maxLen)
    (invariant_dp_values_pos : ∀ k < a.size, 1 ≤ dp[k]!)
    (a_3 : True)
    (invariant_dp_i_pos : 1 ≤ dp_1[i]!)
    (invariant_inner_dp_values_pos : ∀ k < a.size, 1 ≤ dp_1[k]!)
    (invariant_inner_maxLen_pos : 1 ≤ maxLen)
    (if_pos_3 : dp_1[i]! < dp_1[j]! + 1)
    (k₀ : ℕ)
    (hk₀_lt_i : k₀ < i)
    (hk₀_eq_maxLen : dp_1[k₀]! = maxLen)
    (h_k₀_ne_i : ¬k₀ = i)
    (h_i_ne_k₀ : ¬i = k₀)
    : k₀ < dp_1.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_1
    (a : Array ℤ)
    (require_1 : precondition a)
    (dp : Array ℕ)
    (i : ℕ)
    (maxLen : ℕ)
    (a_1 : 1 ≤ i)
    (a_2 : i ≤ a.size)
    (invariant_dp_size : dp.size = a.size)
    (invariant_maxLen_is_max : ∀ k < i, dp[k]! ≤ maxLen)
    (invariant_maxLen_achieved : ∃ k < i, dp[k]! = maxLen)
    (if_pos : i < a.size)
    (dp_1 : Array ℕ)
    (j : ℕ)
    (a_4 : j ≤ i)
    (invariant_inner_dp_size : dp_1.size = a.size)
    (invariant_inner_maxLen_bound : ∀ k < i, dp_1[k]! ≤ maxLen)
    (invariant_inner_maxLen_achieved : ∃ k < i, dp_1[k]! = maxLen)
    (invariant_inner_i_bound : i < a.size)
    (if_pos_1 : j < i)
    (if_pos_2 : a[j]! < a[i]!)
    (if_neg : ¬a = #[])
    (invariant_maxLen_pos : 1 ≤ maxLen)
    (invariant_dp_values_pos : ∀ k < a.size, 1 ≤ dp[k]!)
    (a_3 : True)
    (invariant_dp_i_pos : 1 ≤ dp_1[i]!)
    (invariant_inner_dp_values_pos : ∀ k < a.size, 1 ≤ dp_1[k]!)
    (invariant_inner_maxLen_pos : 1 ≤ maxLen)
    (if_pos_3 : dp_1[i]! < dp_1[j]! + 1)
    (k₀ : ℕ)
    (hk₀_lt_i : k₀ < i)
    (hk₀_eq_maxLen : dp_1[k₀]! = maxLen)
    (h_k₀_ne_i : ¬k₀ = i)
    (h_i_ne_k₀ : ¬i = k₀)
    (h_k₀_lt_size : k₀ < dp_1.size)
    (h_i_lt_size : i < dp_1.size)
    (h_getElem_preserved : (dp_1.setIfInBounds i (dp_1[j]! + 1))[k₀]? = dp_1[k₀]?)
    (h_k₀_some : True)
    (h_modified_size : True)
    (h_k₀_lt_modified_size : k₀ < dp_1.size)
    : (dp_1.setIfInBounds i (dp_1[j]! + 1))[k₀]! = dp_1[k₀]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_2
    (a : Array ℤ)
    (require_1 : precondition a)
    (dp : Array ℕ)
    (i : ℕ)
    (maxLen : ℕ)
    (a_1 : 1 ≤ i)
    (a_2 : i ≤ a.size)
    (invariant_dp_size : dp.size = a.size)
    (invariant_maxLen_is_max : ∀ k < i, dp[k]! ≤ maxLen)
    (invariant_maxLen_achieved : ∃ k < i, dp[k]! = maxLen)
    (if_pos : i < a.size)
    (dp_1 : Array ℕ)
    (j : ℕ)
    (a_4 : j ≤ i)
    (invariant_inner_dp_size : dp_1.size = a.size)
    (invariant_inner_maxLen_bound : ∀ k < i, dp_1[k]! ≤ maxLen)
    (invariant_inner_maxLen_achieved : ∃ k < i, dp_1[k]! = maxLen)
    (invariant_inner_i_bound : i < a.size)
    (if_pos_1 : j < i)
    (if_pos_2 : a[j]! < a[i]!)
    (if_neg : ¬a = #[])
    (invariant_maxLen_pos : 1 ≤ maxLen)
    (invariant_dp_values_pos : ∀ k < a.size, 1 ≤ dp[k]!)
    (a_3 : True)
    (invariant_dp_i_pos : 1 ≤ dp_1[i]!)
    (invariant_inner_dp_values_pos : ∀ k < a.size, 1 ≤ dp_1[k]!)
    (invariant_inner_maxLen_pos : 1 ≤ maxLen)
    (if_pos_3 : dp_1[i]! < dp_1[j]! + 1)
    (k₀ : ℕ)
    (hk₀_lt_i : k₀ < i)
    (hk₀_eq_maxLen : dp_1[k₀]! = maxLen)
    (h_k₀_ne_i : ¬k₀ = i)
    (h_i_ne_k₀ : ¬i = k₀)
    (h_k₀_lt_size : k₀ < dp_1.size)
    (h_i_lt_size : i < dp_1.size)
    (h_getElem_preserved : (dp_1.setIfInBounds i (dp_1[j]! + 1))[k₀]? = dp_1[k₀]?)
    (h_getElem!_eq : (dp_1.setIfInBounds i (dp_1[j]! + 1))[k₀]! = dp_1[k₀]!)
    (h_k₀_some : True)
    (h_modified_size : True)
    (h_k₀_lt_modified_size : k₀ < dp_1.size)
    : (dp_1.setIfInBounds i (dp_1[j]! + 1))[k₀]! = maxLen := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1
    (a : Array ℤ)
    (require_1 : precondition a)
    (dp : Array ℕ)
    (i : ℕ)
    (maxLen : ℕ)
    (a_1 : 1 ≤ i)
    (a_2 : i ≤ a.size)
    (invariant_dp_size : dp.size = a.size)
    (invariant_maxLen_is_max : ∀ k < i, dp[k]! ≤ maxLen)
    (invariant_maxLen_achieved : ∃ k < i, dp[k]! = maxLen)
    (if_pos : i < a.size)
    (dp_1 : Array ℕ)
    (j : ℕ)
    (a_4 : j ≤ i)
    (invariant_inner_dp_size : dp_1.size = a.size)
    (invariant_inner_maxLen_bound : ∀ k < i, dp_1[k]! ≤ maxLen)
    (invariant_inner_maxLen_achieved : ∃ k < i, dp_1[k]! = maxLen)
    (invariant_inner_i_bound : i < a.size)
    (if_pos_1 : j < i)
    (if_pos_2 : a[j]! < a[i]!)
    (if_neg : ¬a = #[])
    (invariant_maxLen_pos : 1 ≤ maxLen)
    (invariant_dp_values_pos : ∀ k < a.size, 1 ≤ dp[k]!)
    (a_3 : True)
    (invariant_dp_i_pos : 1 ≤ dp_1[i]!)
    (invariant_inner_dp_values_pos : ∀ k < a.size, 1 ≤ dp_1[k]!)
    (invariant_inner_maxLen_pos : 1 ≤ maxLen)
    (if_pos_3 : dp_1[i]! < dp_1[j]! + 1)
    : ∃ k < i, (dp_1.setIfInBounds i (dp_1[j]! + 1))[k]! = maxLen := by
    have h_witness : ∃ k < i, dp_1[k]! = maxLen := by (try simp at *; expose_names); exact (invariant_inner_maxLen_achieved); done
    obtain ⟨k₀, hk₀_lt_i, hk₀_eq_maxLen⟩ := h_witness
    have h_k₀_ne_i : k₀ ≠ i := by (try simp at *; expose_names); exact (Nat.ne_of_lt hk₀_lt_i); done
    have h_i_ne_k₀ : i ≠ k₀ := by (try simp at *; expose_names); exact fun a ↦ (h_k₀_ne_i (id (Eq.symm a))); done
    have h_k₀_lt_size : k₀ < dp_1.size := by (try simp at *; expose_names); exact (goal_1_0 a require_1 dp i maxLen a_1 a_2 invariant_dp_size invariant_maxLen_is_max invariant_maxLen_achieved if_pos dp_1 j a_4 invariant_inner_dp_size invariant_inner_maxLen_bound invariant_inner_maxLen_achieved invariant_inner_i_bound if_pos_1 if_pos_2 if_neg invariant_maxLen_pos invariant_dp_values_pos a_3 invariant_dp_i_pos invariant_inner_dp_values_pos invariant_inner_maxLen_pos if_pos_3 k₀ hk₀_lt_i hk₀_eq_maxLen h_k₀_ne_i h_i_ne_k₀); done
    have h_i_lt_size : i < dp_1.size := by (try simp at *; expose_names); exact (Nat.lt_of_lt_of_eq if_pos (id (Eq.symm invariant_inner_dp_size))); done
    have h_getElem_preserved : (dp_1.setIfInBounds i (dp_1[j]! + 1))[k₀]? = dp_1[k₀]? := by (try simp at *; expose_names); exact (Array.getElem?_setIfInBounds_ne h_i_ne_k₀); done
    have h_k₀_some : dp_1[k₀]? = some (dp_1[k₀]'h_k₀_lt_size) := by (try simp at *; expose_names); exact ((Array.getElem?_eq_some_getElem_iff dp_1 k₀ h_k₀_lt_size).mpr require_1); done
    have h_modified_size : (dp_1.setIfInBounds i (dp_1[j]! + 1)).size = dp_1.size := by (try simp at *; expose_names); exact (Array.size_setIfInBounds); done
    have h_k₀_lt_modified_size : k₀ < (dp_1.setIfInBounds i (dp_1[j]! + 1)).size := by (try simp at *; expose_names); exact (h_k₀_lt_size); done
    have h_getElem!_eq : (dp_1.setIfInBounds i (dp_1[j]! + 1))[k₀]! = dp_1[k₀]! := by (try simp at *; expose_names); exact (goal_1_1 a require_1 dp i maxLen a_1 a_2 invariant_dp_size invariant_maxLen_is_max invariant_maxLen_achieved if_pos dp_1 j a_4 invariant_inner_dp_size invariant_inner_maxLen_bound invariant_inner_maxLen_achieved invariant_inner_i_bound if_pos_1 if_pos_2 if_neg invariant_maxLen_pos invariant_dp_values_pos a_3 invariant_dp_i_pos invariant_inner_dp_values_pos invariant_inner_maxLen_pos if_pos_3 k₀ hk₀_lt_i hk₀_eq_maxLen h_k₀_ne_i h_i_ne_k₀ h_k₀_lt_size h_i_lt_size h_getElem_preserved h_k₀_some h_modified_size h_k₀_lt_modified_size); done
    have h_final : (dp_1.setIfInBounds i (dp_1[j]! + 1))[k₀]! = maxLen := by (try simp at *; expose_names); exact (goal_1_2 a require_1 dp i maxLen a_1 a_2 invariant_dp_size invariant_maxLen_is_max invariant_maxLen_achieved if_pos dp_1 j a_4 invariant_inner_dp_size invariant_inner_maxLen_bound invariant_inner_maxLen_achieved invariant_inner_i_bound if_pos_1 if_pos_2 if_neg invariant_maxLen_pos invariant_dp_values_pos a_3 invariant_dp_i_pos invariant_inner_dp_values_pos invariant_inner_maxLen_pos if_pos_3 k₀ hk₀_lt_i hk₀_eq_maxLen h_k₀_ne_i h_i_ne_k₀ h_k₀_lt_size h_i_lt_size h_getElem_preserved h_getElem!_eq h_k₀_some h_modified_size h_k₀_lt_modified_size); done
    exact ⟨k₀, hk₀_lt_i, h_final⟩

theorem goal_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (if_pos : a = #[])
    : postcondition a 0 := by
    sorry


theorem goal_2
    (a : Array ℤ)
    (require_1 : precondition a)
    (dp : Array ℕ)
    (i : ℕ)
    (maxLen : ℕ)
    (a_1 : 1 ≤ i)
    (a_2 : i ≤ a.size)
    (invariant_dp_size : dp.size = a.size)
    (invariant_maxLen_is_max : ∀ k < i, dp[k]! ≤ maxLen)
    (invariant_maxLen_achieved : ∃ k < i, dp[k]! = maxLen)
    (done_1 : i = a.size)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (maxLen_1 : ℕ)
    (if_neg : ¬a = #[])
    (invariant_maxLen_pos : 1 ≤ maxLen)
    (invariant_dp_values_pos : ∀ k < a.size, 1 ≤ dp[k]!)
    (i_3 : dp = i_1 ∧ i = i_2 ∧ maxLen = maxLen_1)
    : postcondition a ↑maxLen_1 := by
    sorry



prove_correct LongestIncreasingSubsequence by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a require_1 if_pos)
  exact (goal_1 a require_1 dp i maxLen a_1 a_2 invariant_dp_size invariant_maxLen_is_max invariant_maxLen_achieved if_pos dp_1 j a_4 invariant_inner_dp_size invariant_inner_maxLen_bound invariant_inner_maxLen_achieved invariant_inner_i_bound if_pos_1 if_pos_2 if_neg invariant_maxLen_pos invariant_dp_values_pos a_3 invariant_dp_i_pos invariant_inner_dp_values_pos invariant_inner_maxLen_pos if_pos_3)
  exact (goal_2 a require_1 dp i maxLen a_1 a_2 invariant_dp_size invariant_maxLen_is_max invariant_maxLen_achieved done_1 i_1 i_2 maxLen_1 if_neg invariant_maxLen_pos invariant_dp_values_pos i_3)
end Proof
