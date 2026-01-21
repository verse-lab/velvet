import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findEvenNumbers: Extract even numbers from an array of integers, preserving order.
    Natural language breakdown:
    1. Input is an array of integers `arr` (may be empty).
    2. Output is an array `result` containing only elements of `arr` that are even.
    3. Every element of `result` is even.
    4. Every even element occurring in `arr` appears in `result` with the same multiplicity.
    5. The relative order of the kept (even) elements is the same as in `arr`.
    6. There are no preconditions.
-/

section Specs
-- Helper predicate: integer evenness.
-- Use `decide` to produce a Bool, so we can keep simple Bool-valued constraints.
def isEvenInt (x : Int) : Bool :=
  decide (x % 2 = 0)

def precondition (arr : Array Int) : Prop :=
  True

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  let l := arr.toList
  let r := result.toList
  -- Order preservation: output is a sublist of the input list.
  r.Sublist l ∧
  -- Only evens are present.
  (∀ x, x ∈ r → isEvenInt x = true) ∧
  -- Exact multiplicity of evens; no odds are included.
  (∀ x,
      (isEvenInt x = true → r.count x = l.count x) ∧
      (isEvenInt x = false → r.count x = 0))
end Specs

section Impl
method findEvenNumbers (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  let mut result : Array Int := (#[] : Array Int)
  let mut i : Nat := 0
  while i < arr.size
    -- Invariant: loop index stays within bounds (needed for safe access and to rewrite take at exit).
    invariant "inv_i_bounds" (i ≤ arr.size)
    -- Invariant: output preserves order and comes from the processed prefix.
    -- At exit, i = arr.size gives result.toList.Sublist arr.toList.
    invariant "inv_sublist_prefix" (result.toList.Sublist (List.take i arr.toList))
    -- Invariant: result contains only even integers (kept in toList form to match postcondition).
    invariant "inv_all_even" (∀ x, x ∈ result.toList → isEvenInt x = true)
    -- Invariant: for any value classified as odd, its multiplicity in result is 0.
    invariant "inv_count_odds_zero" (∀ x, isEvenInt x = false → result.toList.count x = 0)
    -- Invariant: for any even value, multiplicity in result equals multiplicity in the processed prefix.
    -- At exit, i = arr.size yields exact multiplicity for the whole input list.
    invariant "inv_count_evens_prefix" (∀ x, isEvenInt x = true → result.toList.count x = (List.take i arr.toList).count x)
    done_with i = arr.size
  do
    let x := arr[i]!
    if isEvenInt x = true then
      result := result.push x
    i := i + 1
  return result
end Impl

section TestCases
-- Test case 1: example from prompt
-- Input: #[1,2,3,4,5,6] => #[2,4,6]
def test1_arr : Array Int := #[1, 2, 3, 4, 5, 6]
def test1_Expected : Array Int := #[2, 4, 6]

-- Test case 2: mixture with gaps
-- #[7,8,10,13,14] => #[8,10,14]
def test2_arr : Array Int := #[7, 8, 10, 13, 14]
def test2_Expected : Array Int := #[8, 10, 14]

-- Test case 3: all odd => empty
-- #[1,3,5,7] => #[]
def test3_arr : Array Int := #[1, 3, 5, 7]
def test3_Expected : Array Int := #[]

-- Test case 4: empty input => empty output
-- #[] => #[]
def test4_arr : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: includes 0 and negative evens
-- #[0,-2,-3,-4,5] => #[0,-2,-4]
def test5_arr : Array Int := #[0, -2, -3, -4, 5]
def test5_Expected : Array Int := #[0, -2, -4]

-- Test case 6: repeated evens and odds; multiplicity preserved
-- #[2,2,3,2,4,4,5] => #[2,2,2,4,4]
def test6_arr : Array Int := #[2, 2, 3, 2, 4, 4, 5]
def test6_Expected : Array Int := #[2, 2, 2, 4, 4]

-- Test case 7: single element even
-- #[-6] => #[-6]
def test7_arr : Array Int := #[-6]
def test7_Expected : Array Int := #[-6]

-- Test case 8: single element odd
-- #[9] => #[]
def test8_arr : Array Int := #[9]
def test8_Expected : Array Int := #[]

-- Test case 9: alternating parity, preserve relative order
-- #[2,1,4,3,6,5] => #[2,4,6]
def test9_arr : Array Int := #[2, 1, 4, 3, 6, 5]
def test9_Expected : Array Int := #[2, 4, 6]

-- Recommend to validate: test1, test5, test6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((findEvenNumbers test1_arr).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((findEvenNumbers test2_arr).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((findEvenNumbers test3_arr).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((findEvenNumbers test4_arr).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((findEvenNumbers test5_arr).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((findEvenNumbers test6_arr).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((findEvenNumbers test7_arr).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((findEvenNumbers test8_arr).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((findEvenNumbers test9_arr).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 154, Column 0
-- Message: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
-- 
-- Note: Use `set_option maxHeartbeats <num>` to set the limit.
-- 
-- Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-- Line: prove_postcondition_decidable_for findEvenNumbers
-- [ERROR] Line 154, Column 0
-- Message: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
-- 
-- Note: Use `set_option maxHeartbeats <num>` to set the limit.
-- 
-- Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-- Line: prove_postcondition_decidable_for findEvenNumbers
-- [ERROR] Line 155, Column 0
-- Message: failed to synthesize
--   Decidable (postcondition arr result)
-- 
-- Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-- Line: derive_tester_for findEvenNumbers
-- [ERROR] Line 156, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for findEvenNumbers
-- prove_precondition_decidable_for findEvenNumbers
-- prove_postcondition_decidable_for findEvenNumbers
-- derive_tester_for findEvenNumbers
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
--     let res := findEvenNumbersTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct findEvenNumbers by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (if_pos_1 : isEvenInt arr[i]! = true)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (h_len : i < arr.toList.length)
    : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]] := by
    simpa using (List.take_succ_eq_append_getElem (l := arr.toList) (i := i) h_len)

theorem goal_0_1
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (if_pos_1 : isEvenInt arr[i]! = true)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (h_len : i < arr.toList.length)
    (h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]])
    (h_sublist_app : result.toList.Sublist (List.take i arr.toList))
    : (result.toList ++ [arr[i]!]).Sublist (List.take i arr.toList ++ [arr[i]]) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (if_pos_1 : isEvenInt arr[i]! = true)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    : (result.toList ++ [arr[i]!]).Sublist (List.take (i + 1) arr.toList) := by
    have h_len : i < arr.toList.length := by
      (try simp at *; expose_names); exact if_pos; done
    have h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr.toList[i]] := by
      (try simp at *; expose_names); exact (goal_0_0 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos if_pos_1 invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix h_len); done
    have h_sublist_app : (result.toList ++ [arr[i]!]).Sublist (List.take i arr.toList ++ [arr[i]!]) := by
      (try simp at *; expose_names); exact invariant_inv_sublist_prefix; done
    have h_goal' : (result.toList ++ [arr[i]!]).Sublist (List.take i arr.toList ++ [arr.toList[i]]) := by
      (try simp at *; expose_names); exact (goal_0_1 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos if_pos_1 invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix h_len h_take_succ h_sublist_app); done
    simpa [h_take_succ] using h_goal'

theorem goal_1_0
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (if_pos_1 : isEvenInt arr[i]! = true)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (x : ℤ)
    (hx : isEvenInt x = true)
    (h_count_result : Array.count x result = List.count x (List.take i arr.toList))
    (h_len : i < arr.toList.length)
    (h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]])
    (h_count_append : True)
    : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList) + List.count x [arr[i]] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1_1
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (if_pos_1 : isEvenInt arr[i]! = true)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (x : ℤ)
    (hx : isEvenInt x = true)
    (h_count_result : Array.count x result = List.count x (List.take i arr.toList))
    (h_len : i < arr.toList.length)
    (h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]])
    (h_rhs : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList) + List.count x [arr[i]])
    (h_count_append : True)
    : List.count x [arr[i]!] = List.count x [arr[i]] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (if_pos_1 : isEvenInt arr[i]! = true)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    : ∀ (x : ℤ), isEvenInt x = true → Array.count x result + List.count x [arr[i]!] = List.count x (List.take (i + 1) arr.toList) := by
    intro x hx
    have h_count_result : Array.count x result = List.count x (List.take i arr.toList) := by
      (try simp at *; expose_names); exact invariant_inv_count_evens_prefix x hx; done
    have h_len : i < arr.toList.length := by
      (try simp at *; expose_names); exact if_pos; done
    have h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr.toList[i]] := by
      (try simp at *; expose_names); exact (goal_0_0 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos if_pos_1 invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix h_len); done
    have h_count_append : List.count x (List.take i arr.toList ++ [arr.toList[i]]) = List.count x (List.take i arr.toList) + List.count x [arr.toList[i]] := by
      (try simp at *; expose_names); exact List.count_append; done
    have h_rhs : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList) + List.count x [arr.toList[i]] := by
      (try simp at *; expose_names); exact (goal_1_0 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos if_pos_1 invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix x hx h_count_result h_len h_take_succ h_count_append); done
    have h_singleton_simp : List.count x [arr[i]!] = List.count x [arr.toList[i]] := by
      (try simp at *; expose_names); exact (goal_1_1 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos if_pos_1 invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix x hx h_count_result h_len h_take_succ h_rhs h_count_append); done
    calc
      Array.count x result + List.count x [arr[i]!]
          = List.count x (List.take i arr.toList) + List.count x [arr[i]!] := by
              simp [h_count_result]
      _   = List.count x (List.take i arr.toList) + List.count x [arr.toList[i]] := by
              simp [h_singleton_simp]
      _   = List.count x (List.take (i + 1) arr.toList) := by
              simpa [h_rhs] using (Eq.symm h_rhs)

theorem goal_2_0
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (if_neg : isEvenInt arr[i]! = false)
    (x : ℤ)
    (hx : isEvenInt x = true)
    (h_count_prefix : Array.count x result = List.count x (List.take i arr.toList))
    (h_len : i < arr.toList.length)
    : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]] := by
    simpa using (List.take_succ_eq_append_getElem (l := arr.toList) (i := i) h_len)

theorem goal_2_1
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (if_neg : isEvenInt arr[i]! = false)
    (x : ℤ)
    (hx : isEvenInt x = true)
    (h_count_prefix : Array.count x result = List.count x (List.take i arr.toList))
    (h_len : i < arr.toList.length)
    (h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]])
    : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList) + List.count x [arr[i]] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_2
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (if_neg : isEvenInt arr[i]! = false)
    (x : ℤ)
    (hx : isEvenInt x = true)
    (h_count_prefix : Array.count x result = List.count x (List.take i arr.toList))
    (h_len : i < arr.toList.length)
    (h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]])
    (h_idx_eq : arr[i] = arr[i]!)
    (h_singleton_rw : List.count x [arr[i]] = List.count x [arr[i]!])
    (h_count_take_succ : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList) + List.count x [arr[i]])
    (h_count_append : True)
    : ¬x = arr[i]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_3
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (if_neg : isEvenInt arr[i]! = false)
    (x : ℤ)
    (hx : isEvenInt x = true)
    (h_count_prefix : Array.count x result = List.count x (List.take i arr.toList))
    (h_len : i < arr.toList.length)
    (h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]])
    (h_idx_eq : arr[i] = arr[i]!)
    (h_singleton_rw : List.count x [arr[i]] = List.count x [arr[i]!])
    (h_ne : ¬x = arr[i]!)
    (h_count_take_succ : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList) + List.count x [arr[i]])
    (h_count_append : True)
    : List.count x [arr[i]!] = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_4
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (if_neg : isEvenInt arr[i]! = false)
    (x : ℤ)
    (hx : isEvenInt x = true)
    (h_count_prefix : Array.count x result = List.count x (List.take i arr.toList))
    (h_len : i < arr.toList.length)
    (h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]])
    (h_idx_eq : arr[i] = arr[i]!)
    (h_singleton_rw : List.count x [arr[i]] = List.count x [arr[i]!])
    (h_ne : ¬x = arr[i]!)
    (h_count_singleton_zero : List.count x [arr[i]!] = 0)
    (h_count_take_succ : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList) + List.count x [arr[i]])
    (h_count_append : True)
    : List.count x [arr[i]] = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_5
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (if_neg : isEvenInt arr[i]! = false)
    (x : ℤ)
    (hx : isEvenInt x = true)
    (h_count_prefix : Array.count x result = List.count x (List.take i arr.toList))
    (h_len : i < arr.toList.length)
    (h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]])
    (h_idx_eq : arr[i] = arr[i]!)
    (h_singleton_rw : List.count x [arr[i]] = List.count x [arr[i]!])
    (h_ne : ¬x = arr[i]!)
    (h_count_singleton_zero : List.count x [arr[i]!] = 0)
    (h_count_singleton_zero' : List.count x [arr[i]] = 0)
    (h_count_take_succ : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList) + List.count x [arr[i]])
    (h_count_append : True)
    : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (if_pos : i < arr.size)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (if_neg : isEvenInt arr[i]! = false)
    : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take (i + 1) arr.toList) := by
    intro x hx
    have h_count_prefix : Array.count x result = List.count x (List.take i arr.toList) := by
      (try simp at *; expose_names); exact invariant_inv_count_evens_prefix x hx; done
    have h_len : i < arr.toList.length := by
      (try simp at *; expose_names); exact if_pos; done
    have h_take_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr.toList[i]] := by
      (try simp at *; expose_names); exact (goal_2_0 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix if_neg x hx h_count_prefix h_len); done
    have h_count_take_succ : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList ++ [arr.toList[i]]) := by
      (try simp at *; expose_names); exact (goal_2_1 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix if_neg x hx h_count_prefix h_len h_take_succ); done
    have h_count_append : List.count x (List.take i arr.toList ++ [arr.toList[i]]) = List.count x (List.take i arr.toList) + List.count x [arr.toList[i]] := by
      (try simp at *; expose_names); exact List.count_append; done
    have h_idx_eq : arr.toList[i] = arr[i]! := by
      (try simp at *; expose_names); exact Eq.symm (getElem!_pos arr i h_len); done
    have h_singleton_rw : List.count x [arr.toList[i]] = List.count x [arr[i]!] := by
      (try simp at *; expose_names); exact (congrArg (List.count x) (congrFun (congrArg List.cons h_idx_eq) [])); done
    have h_ne : x ≠ arr[i]! := by
      (try simp at *; expose_names); exact (goal_2_2 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix if_neg x hx h_count_prefix h_len h_take_succ h_idx_eq h_singleton_rw h_count_take_succ h_count_append); done
    have h_count_singleton_zero : List.count x [arr[i]!] = 0 := by
      (try simp at *; expose_names); exact (goal_2_3 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix if_neg x hx h_count_prefix h_len h_take_succ h_idx_eq h_singleton_rw h_ne h_count_take_succ h_count_append); done
    have h_count_singleton_zero' : List.count x [arr.toList[i]] = 0 := by
      (try simp at *; expose_names); exact (goal_2_4 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix if_neg x hx h_count_prefix h_len h_take_succ h_idx_eq h_singleton_rw h_ne h_count_singleton_zero h_count_take_succ h_count_append); done
    have h_count_take_succ_eq : List.count x (List.take (i + 1) arr.toList) = List.count x (List.take i arr.toList) := by
      (try simp at *; expose_names); exact (goal_2_5 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix if_neg x hx h_count_prefix h_len h_take_succ h_idx_eq h_singleton_rw h_ne h_count_singleton_zero h_count_singleton_zero' h_count_take_succ h_count_append); done
    calc
      Array.count x result
          = List.count x (List.take i arr.toList) := by
              simpa using h_count_prefix
      _   = List.count x (List.take (i + 1) arr.toList) := by
              simpa [h_count_take_succ_eq] using (Eq.symm h_count_take_succ_eq)

theorem goal_3
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (result : Array ℤ)
    (invariant_inv_i_bounds : i ≤ arr.size)
    (invariant_inv_sublist_prefix : result.toList.Sublist (List.take i arr.toList))
    (done_1 : i = arr.size)
    (i_1 : ℕ)
    (result_1 : Array ℤ)
    (invariant_inv_all_even : ∀ x ∈ result, isEvenInt x = true)
    (invariant_inv_count_odds_zero : ∀ (x : ℤ), isEvenInt x = false → Array.count x result = 0)
    (invariant_inv_count_evens_prefix : ∀ (x : ℤ), isEvenInt x = true → Array.count x result = List.count x (List.take i arr.toList))
    (i_2 : i = i_1 ∧ result = result_1)
    : postcondition arr result_1 := by
    rcases i_2 with ⟨hi, hres⟩
    have htake : List.take i arr.toList = arr.toList := by
      calc
        List.take i arr.toList
            = List.take arr.size arr.toList := by simpa [done_1]
        _ = List.take arr.toList.length arr.toList := by
              -- avoid simp recursion by rewriting length_toList
              simpa [Array.length_toList] using rfl
        _ = arr.toList := by simpa using (List.take_length (l := arr.toList))

    unfold postcondition
    constructor
    · -- sublist
      have : result.toList.Sublist arr.toList := by
        simpa [htake] using invariant_inv_sublist_prefix
      simpa [hres] using this
    constructor
    · -- all outputs even
      intro x hx
      have hxArr1 : x ∈ result_1 := (Array.mem_toList).1 hx
      have hxArr : x ∈ result := by simpa [hres] using hxArr1
      exact invariant_inv_all_even x hxArr
    · -- count properties
      intro x
      constructor
      · intro hxEven
        have hcount : Array.count x result = List.count x (List.take i arr.toList) :=
          invariant_inv_count_evens_prefix x hxEven
        have hcount' : Array.count x result_1 = List.count x arr.toList := by
          simpa [hres, htake] using hcount
        -- convert Array.count to List.count on toList
        -- Array.count_toList: List.count a xs.toList = Array.count a xs
        -- so: result_1.toList.count x = Array.count x result_1
        simpa [Array.count_toList] using hcount'
      · intro hxOdd
        have hcount0 : Array.count x result = 0 :=
          invariant_inv_count_odds_zero x hxOdd
        have hcount0' : Array.count x result_1 = 0 := by
          simpa [hres] using hcount0
        simpa [Array.count_toList] using hcount0'


prove_correct findEvenNumbers by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos if_pos_1 invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix)
  exact (goal_1 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos if_pos_1 invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix)
  exact (goal_2 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix if_pos invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix if_neg)
  exact (goal_3 arr require_1 i result invariant_inv_i_bounds invariant_inv_sublist_prefix done_1 i_1 result_1 invariant_inv_all_even invariant_inv_count_odds_zero invariant_inv_count_evens_prefix i_2)
end Proof
