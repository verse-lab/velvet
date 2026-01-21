import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    firstDuplicate: Find the first duplicate integer in a list when scanning left to right
    Natural language breakdown:
    1. We are given a list of integers
    2. We scan from left to right, looking for the first element that has appeared before
    3. "First duplicate" means the first position j where lst[j] equals some earlier lst[i] (i < j)
    4. We want to find the smallest index j such that lst[j] appears in lst[0..j-1]
    5. The result is the value at that index j
    6. If no such duplicate exists, return none
    7. Edge cases:
       - Empty list: no duplicates, return none
       - Single element: no duplicates, return none
       - All distinct elements: return none
       - Multiple duplicates: return the one with earliest second occurrence
    8. Key insight: We're looking for the first index j where (List.take j lst).contains lst[j]!
-/

section Specs
-- Helper: Check if element at index j appeared in the prefix lst[0..j-1]
-- Using List.take and List.contains as suggested by LeanExplore

-- Postcondition: Characterize the first duplicate
-- When result is some x:
--   - There exists an index j where lst[j]! = x and x appears in lst[0..j-1]
--   - j is the smallest such index (no earlier index has this property)
-- When result is none:
--   - No element appears twice (no index j has lst[j]! in its prefix)

def precondition (lst : List Int) :=
  True  -- no preconditions

def postcondition (lst : List Int) (result : Option Int) :=
  match result with
  | none =>
      -- No element appears in its prefix (no duplicates)
      ∀ j : Nat, j < lst.length → ¬((lst.take j).contains lst[j]!)
  | some x =>
      -- There exists a position j where:
      -- 1. lst[j]! = x
      -- 2. x appears in the prefix lst[0..j-1]
      -- 3. j is minimal (no earlier position has an element appearing in its prefix)
      ∃ j : Nat, j < lst.length ∧
                 lst[j]! = x ∧
                 (lst.take j).contains x ∧
                 (∀ k : Nat, k < j → ¬((lst.take k).contains lst[k]!))
end Specs

section Impl
method firstDuplicate (lst: List Int)
  return (result: Option Int)
  require precondition lst
  ensures postcondition lst result
  do
  let mut i := 0
  let mut found : Option Int := none
  while i < lst.length ∧ found = none
    -- Invariant 1: Index bounds
    -- Init: i = 0, so 0 ≤ i ≤ lst.length holds
    -- Pres: i increments only when i < lst.length, so i ≤ lst.length maintained
    invariant "i_bounds" 0 ≤ i ∧ i ≤ lst.length
    -- Invariant 2: No duplicates found in prefix [0..i)
    -- Init: i = 0, vacuously true
    -- Pres: We only increment i when lst[i]! is not in lst.take i
    invariant "no_dup_prefix" found = none → (∀ k : Nat, k < i → ¬((lst.take k).contains lst[k]!))
    -- Invariant 3: When found = some x, x is the first duplicate with witness
    -- Init: found = none, so vacuously true
    -- Pres: When we set found := some current, current = lst[i]! and (lst.take i).contains current
    invariant "found_valid" ∀ x, found = some x → 
      (∃ j : Nat, j < lst.length ∧ j ≤ i ∧ lst[j]! = x ∧ (lst.take j).contains x ∧ 
        (∀ k : Nat, k < j → ¬((lst.take k).contains lst[k]!)))
    done_with i = lst.length ∨ found ≠ none
  do
    let current := lst[i]!
    let prefixList := lst.take i
    if prefixList.contains current then
      found := some current
    else
      i := i + 1
  return found
end Impl

section TestCases
-- Test case 1: Basic duplicate in middle [1, 2, 3, 2, 4] -> some 2
def test1_lst : List Int := [1, 2, 3, 2, 4]
def test1_Expected : Option Int := some 2

-- Test case 2: Duplicate at end [5, 1, 2, 3, 4, 5] -> some 5
def test2_lst : List Int := [5, 1, 2, 3, 4, 5]
def test2_Expected : Option Int := some 5

-- Test case 3: No duplicates [1, 2, 3, 4, 5] -> none
def test3_lst : List Int := [1, 2, 3, 4, 5]
def test3_Expected : Option Int := none

-- Test case 4: All same elements [7, 7, 7, 7] -> some 7
def test4_lst : List Int := [7, 7, 7, 7]
def test4_Expected : Option Int := some 7

-- Test case 5: Empty list [] -> none
def test5_lst : List Int := []
def test5_Expected : Option Int := none

-- Test case 6: Negative numbers [-1, 2, -1] -> some (-1)
def test6_lst : List Int := [-1, 2, -1]
def test6_Expected : Option Int := some (-1)

-- Test case 7: Single element [42] -> none
def test7_lst : List Int := [42]
def test7_Expected : Option Int := none

-- Test case 8: Two elements, duplicate [3, 3] -> some 3
def test8_lst : List Int := [3, 3]
def test8_Expected : Option Int := some 3

-- Test case 9: Two elements, no duplicate [1, 2] -> none
def test9_lst : List Int := [1, 2]
def test9_Expected : Option Int := none

-- Test case 10: Multiple duplicates, first one wins [1, 2, 1, 2, 3] -> some 1
def test10_lst : List Int := [1, 2, 1, 2, 3]
def test10_Expected : Option Int := some 1

-- Recommend to validate: 1, 4, 6
-- Test 1: Basic case from problem description with duplicate in middle
-- Test 4: Edge case with all same elements (immediate duplicate)
-- Test 6: Tests negative numbers handling
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((firstDuplicate test1_lst).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((firstDuplicate test2_lst).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((firstDuplicate test3_lst).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((firstDuplicate test4_lst).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((firstDuplicate test5_lst).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((firstDuplicate test6_lst).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((firstDuplicate test7_lst).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((firstDuplicate test8_lst).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((firstDuplicate test9_lst).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((firstDuplicate test10_lst).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 171, Column 0
-- Message: unsolved goals
-- lst : List ℤ
-- result : Option ℤ
-- ⊢ Decidable (postcondition lst result)
-- Line: prove_postcondition_decidable_for firstDuplicate
-- [ERROR] Line 173, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for firstDuplicate
-- prove_precondition_decidable_for firstDuplicate
-- prove_postcondition_decidable_for firstDuplicate
-- derive_tester_for firstDuplicate
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (List Int)
--     let res := firstDuplicateTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct firstDuplicate by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (lst : List ℤ)
    (require_1 : precondition lst)
    (found : Option ℤ)
    (i : ℕ)
    (a_1 : i ≤ lst.length)
    (done_1 : i = lst.length ∨ ¬found = none)
    (i_1 : Option ℤ)
    (i_2 : ℕ)
    (a : True)
    (invariant_no_dup_prefix : found = none → ∀ k < i, lst[k]?.getD 0 ∉ List.take k lst)
    (invariant_found_valid : ∀ (x : ℤ), found = some x → ∃ j < lst.length, j ≤ i ∧ lst[j]?.getD 0 = x ∧ x ∈ List.take j lst ∧ ∀ k < j, lst[k]?.getD 0 ∉ List.take k lst)
    (i_3 : found = i_1 ∧ i = i_2)
    : postcondition lst i_1 := by
    unfold postcondition
    obtain ⟨h_found_eq, h_i_eq⟩ := i_3
    subst h_found_eq
    cases hf : found with
    | none =>
      intro j hj
      simp only [List.contains_iff_mem, not_true_eq_false, Bool.not_eq_true, Bool.eq_false_iff]
      -- In the none case, we need to show no duplicates for all j < lst.length
      have h_i_len : i = lst.length := by
        cases done_1 with
        | inl h => exact h
        | inr h => simp [hf] at h
      have h_inv := invariant_no_dup_prefix hf
      specialize h_inv j (by omega)
      simp only [List.getElem!_eq_getElem?_getD]
      exact h_inv
    | some x =>
      -- In the some case, we use invariant_found_valid
      have h_valid := invariant_found_valid x hf
      obtain ⟨j, hj_lt, hj_le_i, hj_eq, hj_mem, hj_min⟩ := h_valid
      refine ⟨j, hj_lt, ?_, ?_, ?_⟩
      · simp only [List.getElem!_eq_getElem?_getD]
        exact hj_eq
      · simp only [List.contains_iff_mem]
        exact hj_mem
      · intro k hk
        simp only [List.contains_iff_mem, not_true_eq_false, Bool.not_eq_true, Bool.eq_false_iff]
        simp only [List.getElem!_eq_getElem?_getD]
        exact hj_min k hk


prove_correct firstDuplicate by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 lst require_1 found i a_1 done_1 i_1 i_2 a invariant_no_dup_prefix invariant_found_valid i_3)
end Proof
