import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- FindSingleNumber: Find the unique element that appears exactly once in a list where all other elements appear exactly twice
--
-- Natural language breakdown:
-- 1. We are given a non-empty list of integers
-- 2. Every element in the list appears exactly twice, except for one element that appears exactly once
-- 3. We need to find and return that unique element that appears only once
-- 4. The precondition ensures the list satisfies this property (one element appears once, all others appear twice)
-- 5. The postcondition ensures the returned result is the element that appears exactly once
-- 6. Using List.count from Mathlib to count occurrences of elements
-- 7. The classic XOR solution works because a ⊕ a = 0 and a ⊕ 0 = a, so all pairs cancel out

section Specs
-- Predicate: the list has valid structure (one element once, all others twice)
def hasValidSingleNumberProperty (nums : List Int) : Prop :=
  nums.length > 0 ∧
  (∃! x, x ∈ nums ∧ nums.count x = 1) ∧
  (∀ x, x ∈ nums → nums.count x = 1 ∨ nums.count x = 2)

-- Predicate: result is the unique element appearing exactly once
def isSingleNumber (nums : List Int) (result : Int) : Prop :=
  result ∈ nums ∧ nums.count result = 1

-- Precondition: list must have valid single number property
def precondition (nums : List Int) :=
  hasValidSingleNumberProperty nums

-- Postcondition: result is the element appearing exactly once
def postcondition (nums : List Int) (result : Int) :=
  isSingleNumber nums result
end Specs

section Impl
method FindSingleNumber (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
    let mut found : Int := nums[0]!
    let mut i : Nat := 0
    while i < nums.length
      -- Invariant 1: i is bounded
      -- Init: i = 0, so 0 ≤ i ≤ nums.length holds
      -- Preservation: i increments by 1 while i < nums.length, so bound maintained
      -- Sufficiency: at exit i = nums.length, combined with other invariants gives postcondition
      invariant "i_bounds" 0 ≤ i ∧ i ≤ nums.length
      -- Invariant 2: found is always a valid element from nums
      -- Init: found = nums[0]! and nums.length > 0 (from precondition)
      -- Preservation: found is only updated to currVal = nums[i]! which is in nums
      -- Sufficiency: ensures result ∈ nums part of postcondition
      invariant "found_in_nums" found ∈ nums
      -- Invariant 3: if we've passed the unique element, found holds it
      -- Init: i = 0 means we haven't processed anything yet, vacuously true for elements before i
      -- Preservation: when we find element with count 1, we set found to it
      -- Sufficiency: at end, combined with uniqueness from precondition, found is THE single number
      invariant "found_is_single" (∃ k, k < i ∧ nums.count nums[k]! = 1) → nums.count found = 1
      done_with i = nums.length
    do
      let currVal := nums[i]!
      -- Manually count occurrences of currVal
      let mut countVal : Nat := 0
      let mut j : Nat := 0
      while j < nums.length
        -- Invariant 1: j is bounded
        -- Init: j = 0
        -- Preservation: j increments by 1 while j < nums.length
        invariant "j_bounds" 0 ≤ j ∧ j ≤ nums.length
        -- Invariant 2: countVal is the count of currVal in nums[0:j]
        -- Init: j = 0, countVal = 0, empty prefix has 0 occurrences
        -- Preservation: if nums[j] = currVal, increment count; otherwise keep same
        invariant "count_partial" countVal = (nums.take j).count currVal
        done_with j = nums.length
      do
        if nums[j]! = currVal then
          countVal := countVal + 1
        j := j + 1
      if countVal = 1 then
        found := currVal
      i := i + 1
    return found
end Impl

section TestCases
-- Test case 1: [2, 2, 3] -> 3 (from problem example)
def test1_nums : List Int := [2, 2, 3]
def test1_Expected : Int := 3

-- Test case 2: [1, 2, 2] -> 1 (from problem example)
def test2_nums : List Int := [1, 2, 2]
def test2_Expected : Int := 1

-- Test case 3: [3, 3, 4, 4, 1] -> 1 (from problem example)
def test3_nums : List Int := [3, 3, 4, 4, 1]
def test3_Expected : Int := 1

-- Test case 4: [0, 1, 3, 1, 3, 88, 88, 100, 100] -> 0 (zero as single number)
def test4_nums : List Int := [0, 1, 3, 1, 3, 88, 88, 100, 100]
def test4_Expected : Int := 0

-- Test case 5: [-1, -1, 7, 9, 7] -> 9 (negative numbers present)
def test5_nums : List Int := [-1, -1, 7, 9, 7]
def test5_Expected : Int := 9

-- Test case 6: single element list
def test6_nums : List Int := [42]
def test6_Expected : Int := 42

-- Test case 7: single number at the beginning
def test7_nums : List Int := [5, 1, 1, 2, 2]
def test7_Expected : Int := 5

-- Test case 8: negative single number
def test8_nums : List Int := [-5, 3, 3]
def test8_Expected : Int := -5

-- Recommend to validate: 1, 3, 6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((FindSingleNumber test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((FindSingleNumber test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((FindSingleNumber test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((FindSingleNumber test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((FindSingleNumber test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((FindSingleNumber test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((FindSingleNumber test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((FindSingleNumber test8_nums).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for FindSingleNumber
prove_precondition_decidable_for FindSingleNumber
prove_postcondition_decidable_for FindSingleNumber
derive_tester_for FindSingleNumber
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (List Int)
    let res := FindSingleNumberTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct FindSingleNumber by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (nums : List ℤ)
    (require_1 : precondition nums)
    (found : ℤ)
    (i : ℕ)
    (a_1 : i ≤ nums.length)
    (invariant_found_in_nums : found ∈ nums)
    (if_pos : i < nums.length)
    (countVal : ℕ)
    (j : ℕ)
    (a_3 : j ≤ nums.length)
    (if_pos_1 : j < nums.length)
    (a : True)
    (invariant_found_is_single : ∀ x < i, List.count (nums[x]?.getD 0) nums = 1 → List.count found nums = 1)
    (a_2 : True)
    (invariant_count_partial : countVal = List.count (nums[i]?.getD 0) (List.take j nums))
    (if_pos_2 : nums[j]?.getD 0 = nums[i]?.getD 0)
    : countVal + 1 = List.count (nums[i]?.getD 0) (List.take (j + 1) nums) := by
    rw [invariant_count_partial]
    rw [List.take_succ]
    rw [List.count_append]
    congr 1
    -- Need to show: List.count (nums[i]?.getD 0) (nums[j]?.toList) = 1
    have h1 : nums[j]? = some nums[j] := List.getElem?_eq_getElem if_pos_1
    simp only [h1, Option.toList_some]
    rw [List.count_singleton]
    have h2 : nums[j] = nums[j]?.getD 0 := by simp [h1, Option.getD_some]
    rw [h2, if_pos_2]
    simp [beq_self_eq_true]

theorem goal_1
    (nums : List ℤ)
    (require_1 : precondition nums)
    (found : ℤ)
    (i : ℕ)
    (a_1 : i ≤ nums.length)
    (invariant_found_in_nums : found ∈ nums)
    (if_pos : i < nums.length)
    (countVal : ℕ)
    (j : ℕ)
    (a_3 : j ≤ nums.length)
    (if_pos_1 : j < nums.length)
    (a : True)
    (invariant_found_is_single : ∀ x < i, List.count (nums[x]?.getD 0) nums = 1 → List.count found nums = 1)
    (a_2 : True)
    (invariant_count_partial : countVal = List.count (nums[i]?.getD 0) (List.take j nums))
    (if_neg : ¬nums[j]?.getD 0 = nums[i]?.getD 0)
    : countVal = List.count (nums[i]?.getD 0) (List.take (j + 1) nums) := by
    rw [List.take_succ]
    rw [List.count_append]
    rw [invariant_count_partial]
    have hj_bound : j < nums.length := if_pos_1
    rw [List.getElem?_eq_getElem hj_bound]
    simp only [Option.toList]
    rw [List.count_singleton]
    have hj_getD : nums[j]?.getD 0 = nums[j] := by
      rw [List.getElem?_eq_getElem hj_bound]
      rfl
    have hne : ¬(nums[j] = nums[i]?.getD 0) := by
      intro heq
      apply if_neg
      rw [hj_getD]
      exact heq
    simp only [beq_iff_eq, hne, ↓reduceIte, Nat.add_zero]

theorem goal_2
    (nums : List ℤ)
    (require_1 : precondition nums)
    : nums[0]?.getD 0 ∈ nums := by
    unfold precondition hasValidSingleNumberProperty at require_1
    obtain ⟨hlen, _, _⟩ := require_1
    have h0 : 0 < nums.length := hlen
    simp only [List.getElem?_eq_getElem h0, Option.getD_some]
    exact List.getElem_mem h0

theorem goal_3
    (nums : List ℤ)
    (require_1 : precondition nums)
    (found : ℤ)
    (i : ℕ)
    (a_1 : i ≤ nums.length)
    (invariant_found_in_nums : found ∈ nums)
    (done_1 : i = nums.length)
    (i_1 : ℤ)
    (i_2 : ℕ)
    (a : True)
    (invariant_found_is_single : ∀ x < i, List.count (nums[x]?.getD 0) nums = 1 → List.count found nums = 1)
    (i_3 : found = i_1 ∧ i = i_2)
    : postcondition nums i_1 := by
    unfold postcondition isSingleNumber
    obtain ⟨found_eq_i1, _⟩ := i_3
    rw [← found_eq_i1]
    constructor
    · exact invariant_found_in_nums
    · -- Need to show nums.count found = 1
      -- From precondition, there exists exactly one element with count 1
      unfold precondition hasValidSingleNumberProperty at require_1
      obtain ⟨len_pos, ⟨unique_single, all_counts⟩⟩ := require_1
      -- unique_single : ∃! x, x ∈ nums ∧ nums.count x = 1
      obtain ⟨witness, ⟨wit_in_nums, wit_count_1⟩, _⟩ := unique_single
      -- witness is in nums with count 1, so there's some index k where nums[k] = witness
      have wit_mem := wit_in_nums
      rw [List.mem_iff_getElem] at wit_mem
      obtain ⟨k, hk, hk_eq⟩ := wit_mem
      -- At index k, nums[k] = witness has count 1
      have count_at_k : List.count (nums[k]?.getD 0) nums = 1 := by
        simp only [List.getElem?_eq_getElem hk, Option.getD_some]
        rw [hk_eq]
        exact wit_count_1
      -- Since i = nums.length and k < nums.length = i
      have k_lt_i : k < i := by omega
      -- Apply invariant_found_is_single
      exact invariant_found_is_single k k_lt_i count_at_k


prove_correct FindSingleNumber by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 nums require_1 found i a_1 invariant_found_in_nums if_pos countVal j a_3 if_pos_1 a invariant_found_is_single a_2 invariant_count_partial if_pos_2)
  exact (goal_1 nums require_1 found i a_1 invariant_found_in_nums if_pos countVal j a_3 if_pos_1 a invariant_found_is_single a_2 invariant_count_partial if_neg)
  exact (goal_2 nums require_1)
  exact (goal_3 nums require_1 found i a_1 invariant_found_in_nums done_1 i_1 i_2 a invariant_found_is_single i_3)
end Proof
