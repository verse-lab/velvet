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
    findProduct: product of the first even and the first odd integer encountered in a list
    Natural language breakdown:
    1. Input is a list of integers `lst`.
    2. We scan `lst` from left to right.
    3. The "first even" is the leftmost element of `lst` whose remainder modulo 2 is 0.
    4. The "first odd" is the leftmost element of `lst` whose remainder modulo 2 is not 0.
    5. The output is the product (in `Int`) of these two first elements.
    6. Precondition: `lst` contains at least one even integer and at least one odd integer.
    7. The result must equal (firstEven * firstOdd) where each is the respective leftmost witness.
-/

section Specs
-- Helper predicates as Bool for use with `List.find?`.
-- We define parity via `Int` modulo and boolean equality.

def isEven (z : Int) : Bool := (z % 2) == 0

def isOdd (z : Int) : Bool := (z % 2) != 0

-- Precondition: at least one even and at least one odd exists in the list.
-- Using `find?` makes the "first" (leftmost) notion precise.

def precondition (lst : List Int) : Prop :=
  (lst.find? isEven).isSome ∧ (lst.find? isOdd).isSome

-- Postcondition: result is the product of the first even and the first odd found.

def postcondition (lst : List Int) (result : Int) : Prop :=
  ∃ (e : Int) (o : Int),
    lst.find? isEven = some e ∧
    lst.find? isOdd = some o ∧
    result = e * o
end Specs

section Impl
method findProduct (lst : List Int) return (result : Int)
  require precondition lst
  ensures postcondition lst result
  do
  -- Imperatively scan left-to-right, remembering the first even and the first odd.
  let mut xs := lst
  let mut foundEven : Bool := false
  let mut foundOdd : Bool := false
  let mut firstEven : Int := 0
  let mut firstOdd : Int := 0

  while (foundEven = false ∨ foundOdd = false)
    -- Invariant: xs is always a suffix of the original list (we only drop the head).
    -- Init: xs=lst (take pref=[]). Preserved: if lst = pref ++ (y::ys) then lst = (pref++[y]) ++ ys.
    invariant "inv_xs_suffix" (∃ pref : List Int, lst = pref ++ xs)

    -- Invariant: if we have not yet found an even, then the first even of lst is still in xs.
    -- Init: xs=lst and precondition gives find? isEven lst isSome.
    -- Preserved: if foundEven stays false, we only drop a head y with isEven y = false, so the first even cannot be dropped.
    invariant "inv_firstEven_still_in_suffix_if_not_found" (foundEven = false → lst.find? isEven = xs.find? isEven)

    -- Invariant: if we have not yet found an odd, then the first odd of lst is still in xs.
    invariant "inv_firstOdd_still_in_suffix_if_not_found" (foundOdd = false → lst.find? isOdd = xs.find? isOdd)

    -- Invariant: if we have not yet found an even, there is still an even in the remaining suffix.
    -- This guarantees progress / non-stuckness when xs becomes [].
    invariant "inv_even_still_in_suffix" (foundEven = false → (xs.find? isEven).isSome)

    -- Invariant: if we have not yet found an odd, there is still an odd in the remaining suffix.
    invariant "inv_odd_still_in_suffix" (foundOdd = false → (xs.find? isOdd).isSome)

    -- Invariant: once foundEven is set, firstEven equals the first even in the original list.
    -- Init: vacuous. Preserved: after setting foundEven/firstEven once, we never change them.
    invariant "inv_firstEven_is_global_first" (foundEven = true → lst.find? isEven = some firstEven)

    -- Invariant: once foundOdd is set, firstOdd equals the first odd in the original list.
    invariant "inv_firstOdd_is_global_first" (foundOdd = true → lst.find? isOdd = some firstOdd)

    done_with (foundEven = true ∧ foundOdd = true)
  do
    match xs with
    | [] =>
      -- Unreachable: if either flag is false, the corresponding find? in xs must be Some.
      foundEven := true
      foundOdd := true
    | y :: ys =>
      if (foundEven = false) then
        if isEven y then
          firstEven := y
          foundEven := true
      if (foundOdd = false) then
        if isOdd y then
          firstOdd := y
          foundOdd := true
      xs := ys

  let prod := firstEven * firstOdd
  return prod
end Impl

section TestCases
-- Test case 1: example from prompt
def test1_lst : List Int := [2, 3, 4, 5]
def test1_Expected : Int := 6

-- Test case 2: first even early, first odd appears later
def test2_lst : List Int := [2, 4, 3, 6]
def test2_Expected : Int := 6

-- Test case 3: first odd occurs before first even
def test3_lst : List Int := [1, 2, 5, 4]
def test3_Expected : Int := 2

-- Test case 4: negatives included
def test4_lst : List Int := [-3, -2, 6, 5]
def test4_Expected : Int := 6

-- Test case 5: zero as first even
def test5_lst : List Int := [0, 7, 2, 9]
def test5_Expected : Int := 0

-- Test case 6: first odd is negative
def test6_lst : List Int := [4, -5, 8, 3]
def test6_Expected : Int := -20

-- Test case 7: single even and single odd, minimal length satisfying precondition
def test7_lst : List Int := [2, 1]
def test7_Expected : Int := 2

-- Test case 8: duplicates; first occurrences matter
def test8_lst : List Int := [6, 6, 9, 9]
def test8_Expected : Int := 54

-- Test case 9: odd first, even later, with more elements
def test9_lst : List Int := [5, 7, 8, 10, 11]
def test9_Expected : Int := 40

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 3, 6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((findProduct test1_lst).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((findProduct test2_lst).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((findProduct test3_lst).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((findProduct test4_lst).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((findProduct test5_lst).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((findProduct test6_lst).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((findProduct test7_lst).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((findProduct test8_lst).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((findProduct test9_lst).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 144, Column 0
-- Message: unsolved goals
-- lst : List ℤ
-- result : ℤ
-- ⊢ Decidable (postcondition lst result)
-- Line: prove_postcondition_decidable_for findProduct
-- [ERROR] Line 146, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for findProduct
-- prove_precondition_decidable_for findProduct
-- prove_postcondition_decidable_for findProduct
-- derive_tester_for findProduct
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (List Int)
--     let res := findProductTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct findProduct by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (lst : List ℤ)
    (require_1 : precondition lst)
    (firstEven : ℤ)
    (firstOdd : ℤ)
    (foundEven : Bool)
    (foundOdd : Bool)
    (xs : List ℤ)
    (invariant_inv_xs_suffix : ∃ pref, lst = pref ++ xs)
    (invariant_inv_firstEven_still_in_suffix_if_not_found : foundEven = false → List.find? isEven lst = List.find? isEven xs)
    (invariant_inv_firstOdd_still_in_suffix_if_not_found : foundOdd = false → List.find? isOdd lst = List.find? isOdd xs)
    (invariant_inv_firstEven_is_global_first : foundEven = true → List.find? isEven lst = some firstEven)
    (invariant_inv_firstOdd_is_global_first : foundOdd = true → List.find? isOdd lst = some firstOdd)
    (if_pos : foundEven = false ∨ foundOdd = false)
    (i : ℤ)
    (i_1 : List ℤ)
    (i_2 : xs = i :: i_1)
    (if_pos_1 : foundEven = false)
    (if_pos_2 : isEven i = true)
    (if_pos_3 : foundOdd = false)
    (if_pos_4 : isOdd i = true)
    (invariant_inv_even_still_in_suffix : foundEven = false → ∃ x ∈ xs, isEven x = true)
    (invariant_inv_odd_still_in_suffix : foundOdd = false → ∃ x ∈ xs, isOdd x = true)
    : ∃ pref, lst = pref ++ i_1 := by
    rcases invariant_inv_xs_suffix with ⟨pref, hpref⟩
    refine ⟨pref ++ [i], ?_⟩
    -- rewrite `xs` as `i :: i_1`, then reassociate to expose suffix `i_1`
    calc
      lst = pref ++ xs := hpref
      _ = pref ++ (i :: i_1) := by simpa [i_2]
      _ = (pref ++ [i]) ++ i_1 := by
            -- `pref ++ (i :: i_1) = pref ++ [i] ++ i_1` and then reassociate
            simpa [List.append_assoc] using (List.append_cons pref i i_1)

theorem goal_1
    (lst : List ℤ)
    (require_1 : precondition lst)
    (firstEven : ℤ)
    (firstOdd : ℤ)
    (foundEven : Bool)
    (foundOdd : Bool)
    (xs : List ℤ)
    (invariant_inv_xs_suffix : ∃ pref, lst = pref ++ xs)
    (invariant_inv_firstEven_still_in_suffix_if_not_found : foundEven = false → List.find? isEven lst = List.find? isEven xs)
    (invariant_inv_firstOdd_still_in_suffix_if_not_found : foundOdd = false → List.find? isOdd lst = List.find? isOdd xs)
    (invariant_inv_firstEven_is_global_first : foundEven = true → List.find? isEven lst = some firstEven)
    (invariant_inv_firstOdd_is_global_first : foundOdd = true → List.find? isOdd lst = some firstOdd)
    (if_pos : foundEven = false ∨ foundOdd = false)
    (i : ℤ)
    (i_1 : List ℤ)
    (i_2 : xs = i :: i_1)
    (if_pos_1 : foundEven = false)
    (if_pos_2 : isEven i = true)
    (if_pos_3 : foundOdd = false)
    (invariant_inv_even_still_in_suffix : foundEven = false → ∃ x ∈ xs, isEven x = true)
    (invariant_inv_odd_still_in_suffix : foundOdd = false → ∃ x ∈ xs, isOdd x = true)
    (if_neg : isOdd i = false)
    : ∃ pref, lst = pref ++ i_1 := by
    rcases invariant_inv_xs_suffix with ⟨pref, hpref⟩
    refine ⟨pref ++ [i], ?_⟩
    -- rewrite xs as i :: i_1 and reassociate
    calc
      lst = pref ++ xs := hpref
      _ = pref ++ (i :: i_1) := by simpa [i_2]
      _ = (pref ++ [i]) ++ i_1 := by
            simpa [List.append_assoc] using (List.append_cons pref i i_1)

theorem goal_2
    (lst : List ℤ)
    (require_1 : precondition lst)
    (firstEven : ℤ)
    (firstOdd : ℤ)
    (foundEven : Bool)
    (foundOdd : Bool)
    (xs : List ℤ)
    (invariant_inv_xs_suffix : ∃ pref, lst = pref ++ xs)
    (invariant_inv_firstEven_still_in_suffix_if_not_found : foundEven = false → List.find? isEven lst = List.find? isEven xs)
    (invariant_inv_firstOdd_still_in_suffix_if_not_found : foundOdd = false → List.find? isOdd lst = List.find? isOdd xs)
    (invariant_inv_firstEven_is_global_first : foundEven = true → List.find? isEven lst = some firstEven)
    (invariant_inv_firstOdd_is_global_first : foundOdd = true → List.find? isOdd lst = some firstOdd)
    (if_pos : foundEven = false ∨ foundOdd = false)
    (i : ℤ)
    (i_1 : List ℤ)
    (i_2 : xs = i :: i_1)
    (if_pos_1 : foundEven = false)
    (if_pos_2 : isEven i = true)
    (invariant_inv_even_still_in_suffix : foundEven = false → ∃ x ∈ xs, isEven x = true)
    (invariant_inv_odd_still_in_suffix : foundOdd = false → ∃ x ∈ xs, isOdd x = true)
    (if_neg : foundOdd = true)
    : ∃ pref, lst = pref ++ i_1 := by
    rcases invariant_inv_xs_suffix with ⟨pref, hpref⟩
    refine ⟨pref ++ [i], ?_⟩
    -- lst = pref ++ xs = pref ++ (i :: i_1) = pref ++ [i] ++ i_1 = (pref ++ [i]) ++ i_1
    calc
      lst = pref ++ xs := hpref
      _ = pref ++ (i :: i_1) := by simpa [i_2]
      _ = pref ++ [i] ++ i_1 := by simpa using (List.append_cons pref i i_1)
      _ = (pref ++ [i]) ++ i_1 := by simp [List.append_assoc]

theorem goal_3
    (lst : List ℤ)
    (require_1 : precondition lst)
    (firstEven : ℤ)
    (firstOdd : ℤ)
    (foundEven : Bool)
    (foundOdd : Bool)
    (xs : List ℤ)
    (invariant_inv_xs_suffix : ∃ pref, lst = pref ++ xs)
    (invariant_inv_firstEven_still_in_suffix_if_not_found : foundEven = false → List.find? isEven lst = List.find? isEven xs)
    (invariant_inv_firstOdd_still_in_suffix_if_not_found : foundOdd = false → List.find? isOdd lst = List.find? isOdd xs)
    (invariant_inv_firstEven_is_global_first : foundEven = true → List.find? isEven lst = some firstEven)
    (invariant_inv_firstOdd_is_global_first : foundOdd = true → List.find? isOdd lst = some firstOdd)
    (if_pos : foundEven = false ∨ foundOdd = false)
    (i : ℤ)
    (i_1 : List ℤ)
    (i_2 : xs = i :: i_1)
    (if_pos_1 : foundEven = false)
    (if_pos_2 : foundOdd = false)
    (if_pos_3 : isOdd i = true)
    (invariant_inv_even_still_in_suffix : foundEven = false → ∃ x ∈ xs, isEven x = true)
    (invariant_inv_odd_still_in_suffix : foundOdd = false → ∃ x ∈ xs, isOdd x = true)
    (if_neg : isEven i = false)
    : ∃ pref, lst = pref ++ i_1 := by
    rcases invariant_inv_xs_suffix with ⟨pref, hpref⟩
    refine ⟨pref ++ [i], ?_⟩
    -- rewrite `xs` as `i :: i_1` and reassociate appends
    calc
      lst = pref ++ xs := hpref
      _ = pref ++ (i :: i_1) := by simpa [i_2]
      _ = (pref ++ [i]) ++ i_1 := by
            simpa [List.append_assoc] using (List.append_cons pref i i_1)

theorem goal_4
    (lst : List ℤ)
    (require_1 : precondition lst)
    (firstEven : ℤ)
    (firstOdd : ℤ)
    (foundEven : Bool)
    (foundOdd : Bool)
    (xs : List ℤ)
    (invariant_inv_xs_suffix : ∃ pref, lst = pref ++ xs)
    (invariant_inv_firstEven_still_in_suffix_if_not_found : foundEven = false → List.find? isEven lst = List.find? isEven xs)
    (invariant_inv_firstOdd_still_in_suffix_if_not_found : foundOdd = false → List.find? isOdd lst = List.find? isOdd xs)
    (invariant_inv_firstEven_is_global_first : foundEven = true → List.find? isEven lst = some firstEven)
    (invariant_inv_firstOdd_is_global_first : foundOdd = true → List.find? isOdd lst = some firstOdd)
    (if_pos : foundEven = false ∨ foundOdd = false)
    (i : ℤ)
    (i_1 : List ℤ)
    (i_2 : xs = i :: i_1)
    (if_pos_1 : foundEven = false)
    (if_pos_2 : foundOdd = false)
    (invariant_inv_even_still_in_suffix : foundEven = false → ∃ x ∈ xs, isEven x = true)
    (invariant_inv_odd_still_in_suffix : foundOdd = false → ∃ x ∈ xs, isOdd x = true)
    (if_neg : isEven i = false)
    (if_neg_1 : isOdd i = false)
    : ∃ pref, lst = pref ++ i_1 := by
    rcases invariant_inv_xs_suffix with ⟨pref, hpref⟩
    refine ⟨pref ++ [i], ?_⟩
    -- rewrite `xs` as `i :: i_1`, then reassociate
    calc
      lst = pref ++ xs := hpref
      _ = pref ++ (i :: i_1) := by simpa [i_2]
      _ = pref ++ [i] ++ i_1 := by simpa using (List.append_cons pref i i_1)
      _ = (pref ++ [i]) ++ i_1 := by
            simpa [List.append_assoc]

theorem goal_5
    (lst : List ℤ)
    (require_1 : precondition lst)
    (firstEven : ℤ)
    (firstOdd : ℤ)
    (foundEven : Bool)
    (foundOdd : Bool)
    (xs : List ℤ)
    (invariant_inv_xs_suffix : ∃ pref, lst = pref ++ xs)
    (invariant_inv_firstEven_still_in_suffix_if_not_found : foundEven = false → List.find? isEven lst = List.find? isEven xs)
    (invariant_inv_firstOdd_still_in_suffix_if_not_found : foundOdd = false → List.find? isOdd lst = List.find? isOdd xs)
    (invariant_inv_firstEven_is_global_first : foundEven = true → List.find? isEven lst = some firstEven)
    (invariant_inv_firstOdd_is_global_first : foundOdd = true → List.find? isOdd lst = some firstOdd)
    (if_pos : foundEven = false ∨ foundOdd = false)
    (i : ℤ)
    (i_1 : List ℤ)
    (i_2 : xs = i :: i_1)
    (if_pos_1 : foundEven = false)
    (invariant_inv_even_still_in_suffix : foundEven = false → ∃ x ∈ xs, isEven x = true)
    (invariant_inv_odd_still_in_suffix : foundOdd = false → ∃ x ∈ xs, isOdd x = true)
    (if_neg : isEven i = false)
    (if_neg_1 : foundOdd = true)
    : ∃ pref, lst = pref ++ i_1 := by
    rcases invariant_inv_xs_suffix with ⟨pref0, hlst⟩
    refine ⟨pref0 ++ [i], ?_⟩
    -- rewrite the suffix `xs` as `i :: i_1` and reassociate
    calc
      lst = pref0 ++ xs := hlst
      _ = pref0 ++ (i :: i_1) := by simpa [i_2]
      _ = (pref0 ++ [i]) ++ i_1 := by
            simpa [List.append_assoc] using (List.append_cons pref0 i i_1)

theorem goal_6
    (lst : List ℤ)
    (require_1 : precondition lst)
    (firstEven : ℤ)
    (firstOdd : ℤ)
    (foundEven : Bool)
    (foundOdd : Bool)
    (xs : List ℤ)
    (invariant_inv_xs_suffix : ∃ pref, lst = pref ++ xs)
    (invariant_inv_firstEven_still_in_suffix_if_not_found : foundEven = false → List.find? isEven lst = List.find? isEven xs)
    (invariant_inv_firstOdd_still_in_suffix_if_not_found : foundOdd = false → List.find? isOdd lst = List.find? isOdd xs)
    (invariant_inv_firstEven_is_global_first : foundEven = true → List.find? isEven lst = some firstEven)
    (invariant_inv_firstOdd_is_global_first : foundOdd = true → List.find? isOdd lst = some firstOdd)
    (if_pos : foundEven = false ∨ foundOdd = false)
    (i : ℤ)
    (i_1 : List ℤ)
    (i_2 : xs = i :: i_1)
    (if_pos_1 : foundOdd = false)
    (if_pos_2 : isOdd i = true)
    (invariant_inv_even_still_in_suffix : foundEven = false → ∃ x ∈ xs, isEven x = true)
    (invariant_inv_odd_still_in_suffix : foundOdd = false → ∃ x ∈ xs, isOdd x = true)
    (if_neg : foundEven = true)
    : ∃ pref, lst = pref ++ i_1 := by
    rcases invariant_inv_xs_suffix with ⟨pref0, hlst⟩
    refine ⟨pref0 ++ [i], ?_⟩
    -- rewrite using xs = i :: i_1, then reassociate
    calc
      lst = pref0 ++ xs := hlst
      _ = pref0 ++ (i :: i_1) := by simpa [i_2]
      _ = pref0 ++ [i] ++ i_1 := by simpa using (List.append_cons pref0 i i_1)
      _ = (pref0 ++ [i]) ++ i_1 := by simp [List.append_assoc]

theorem goal_7
    (lst : List ℤ)
    (require_1 : precondition lst)
    (firstEven : ℤ)
    (firstOdd : ℤ)
    (foundEven : Bool)
    (foundOdd : Bool)
    (xs : List ℤ)
    (invariant_inv_xs_suffix : ∃ pref, lst = pref ++ xs)
    (invariant_inv_firstEven_still_in_suffix_if_not_found : foundEven = false → List.find? isEven lst = List.find? isEven xs)
    (invariant_inv_firstOdd_still_in_suffix_if_not_found : foundOdd = false → List.find? isOdd lst = List.find? isOdd xs)
    (invariant_inv_firstEven_is_global_first : foundEven = true → List.find? isEven lst = some firstEven)
    (invariant_inv_firstOdd_is_global_first : foundOdd = true → List.find? isOdd lst = some firstOdd)
    (if_pos : foundEven = false ∨ foundOdd = false)
    (i : ℤ)
    (i_1 : List ℤ)
    (i_2 : xs = i :: i_1)
    (if_pos_1 : foundOdd = false)
    (invariant_inv_even_still_in_suffix : foundEven = false → ∃ x ∈ xs, isEven x = true)
    (invariant_inv_odd_still_in_suffix : foundOdd = false → ∃ x ∈ xs, isOdd x = true)
    (if_neg : foundEven = true)
    (if_neg_1 : isOdd i = false)
    : ∃ pref, lst = pref ++ i_1 := by
    rcases invariant_inv_xs_suffix with ⟨pref0, hlst⟩
    refine ⟨pref0 ++ [i], ?_⟩
    -- use xs = i :: i_1 and rewrite append with cons
    calc
      lst = pref0 ++ xs := hlst
      _ = pref0 ++ (i :: i_1) := by simpa [i_2]
      _ = (pref0 ++ [i]) ++ i_1 := by
        -- `List.append_cons` gives: pref0 ++ (i :: i_1) = pref0 ++ [i] ++ i_1
        -- then reassociate to match `(pref0 ++ [i]) ++ i_1`
        simpa [List.append_assoc] using (List.append_cons pref0 i i_1).symm

theorem goal_8
    (lst : List ℤ)
    (require_1 : precondition lst)
    : ∃ pref, lst = pref ++ lst := by
    refine ⟨[], ?_⟩
    simp

theorem goal_9
    (lst : List ℤ)
    (require_1 : precondition lst)
    : ∃ x ∈ lst, isEven x = true := by
  unfold precondition at require_1
  have hEvenSome : (lst.find? isEven).isSome := require_1.1
  have hEvenExists : ∃ x, x ∈ lst ∧ isEven x := by
    simpa using (List.find?_isSome (xs := lst) (p := isEven)).1 hEvenSome
  rcases hEvenExists with ⟨x, hxmem, hxEven⟩
  refine ⟨x, hxmem, ?_⟩
  simpa using hxEven

theorem goal_10
    (lst : List ℤ)
    (require_1 : precondition lst)
    : ∃ x ∈ lst, isOdd x = true := by
  unfold precondition at require_1
  have hOddSome : (lst.find? isOdd).isSome := require_1.2
  have hOddExists : ∃ x, x ∈ lst ∧ isOdd x := (List.find?_isSome).1 hOddSome
  rcases hOddExists with ⟨x, hxmem, hxOdd⟩
  refine ⟨x, hxmem, ?_⟩
  simpa using hxOdd

theorem goal_11
    (lst : List ℤ)
    (require_1 : precondition lst)
    (firstEven : ℤ)
    (firstOdd : ℤ)
    (foundEven : Bool)
    (foundOdd : Bool)
    (xs : List ℤ)
    (invariant_inv_xs_suffix : ∃ pref, lst = pref ++ xs)
    (invariant_inv_firstEven_still_in_suffix_if_not_found : foundEven = false → List.find? isEven lst = List.find? isEven xs)
    (invariant_inv_firstOdd_still_in_suffix_if_not_found : foundOdd = false → List.find? isOdd lst = List.find? isOdd xs)
    (invariant_inv_firstEven_is_global_first : foundEven = true → List.find? isEven lst = some firstEven)
    (invariant_inv_firstOdd_is_global_first : foundOdd = true → List.find? isOdd lst = some firstOdd)
    (a : foundEven = true)
    (a_1 : foundOdd = true)
    (i : ℤ)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : Bool)
    (xs_1 : List ℤ)
    (invariant_inv_even_still_in_suffix : foundEven = false → ∃ x ∈ xs, isEven x = true)
    (invariant_inv_odd_still_in_suffix : foundOdd = false → ∃ x ∈ xs, isOdd x = true)
    (i_4 : firstEven = i ∧ firstOdd = i_1 ∧ foundEven = i_2 ∧ foundOdd = i_3 ∧ xs = xs_1)
    : postcondition lst (i * i_1) := by
    rcases i_4 with ⟨hFE, hrest⟩
    rcases hrest with ⟨hFO, -⟩

    have hEven : List.find? isEven lst = some firstEven :=
      invariant_inv_firstEven_is_global_first a
    have hOdd : List.find? isOdd lst = some firstOdd :=
      invariant_inv_firstOdd_is_global_first a_1

    refine ⟨i, i_1, ?_, ?_, ?_⟩
    · simpa [hFE] using hEven
    · simpa [hFO] using hOdd
    · rfl


prove_correct findProduct by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 lst require_1 firstEven firstOdd foundEven foundOdd xs invariant_inv_xs_suffix invariant_inv_firstEven_still_in_suffix_if_not_found invariant_inv_firstOdd_still_in_suffix_if_not_found invariant_inv_firstEven_is_global_first invariant_inv_firstOdd_is_global_first if_pos i i_1 i_2 if_pos_1 if_pos_2 if_pos_3 if_pos_4 invariant_inv_even_still_in_suffix invariant_inv_odd_still_in_suffix)
  exact (goal_1 lst require_1 firstEven firstOdd foundEven foundOdd xs invariant_inv_xs_suffix invariant_inv_firstEven_still_in_suffix_if_not_found invariant_inv_firstOdd_still_in_suffix_if_not_found invariant_inv_firstEven_is_global_first invariant_inv_firstOdd_is_global_first if_pos i i_1 i_2 if_pos_1 if_pos_2 if_pos_3 invariant_inv_even_still_in_suffix invariant_inv_odd_still_in_suffix if_neg)
  exact (goal_2 lst require_1 firstEven firstOdd foundEven foundOdd xs invariant_inv_xs_suffix invariant_inv_firstEven_still_in_suffix_if_not_found invariant_inv_firstOdd_still_in_suffix_if_not_found invariant_inv_firstEven_is_global_first invariant_inv_firstOdd_is_global_first if_pos i i_1 i_2 if_pos_1 if_pos_2 invariant_inv_even_still_in_suffix invariant_inv_odd_still_in_suffix if_neg)
  exact (goal_3 lst require_1 firstEven firstOdd foundEven foundOdd xs invariant_inv_xs_suffix invariant_inv_firstEven_still_in_suffix_if_not_found invariant_inv_firstOdd_still_in_suffix_if_not_found invariant_inv_firstEven_is_global_first invariant_inv_firstOdd_is_global_first if_pos i i_1 i_2 if_pos_1 if_pos_2 if_pos_3 invariant_inv_even_still_in_suffix invariant_inv_odd_still_in_suffix if_neg)
  exact (goal_4 lst require_1 firstEven firstOdd foundEven foundOdd xs invariant_inv_xs_suffix invariant_inv_firstEven_still_in_suffix_if_not_found invariant_inv_firstOdd_still_in_suffix_if_not_found invariant_inv_firstEven_is_global_first invariant_inv_firstOdd_is_global_first if_pos i i_1 i_2 if_pos_1 if_pos_2 invariant_inv_even_still_in_suffix invariant_inv_odd_still_in_suffix if_neg if_neg_1)
  exact (goal_5 lst require_1 firstEven firstOdd foundEven foundOdd xs invariant_inv_xs_suffix invariant_inv_firstEven_still_in_suffix_if_not_found invariant_inv_firstOdd_still_in_suffix_if_not_found invariant_inv_firstEven_is_global_first invariant_inv_firstOdd_is_global_first if_pos i i_1 i_2 if_pos_1 invariant_inv_even_still_in_suffix invariant_inv_odd_still_in_suffix if_neg if_neg_1)
  exact (goal_6 lst require_1 firstEven firstOdd foundEven foundOdd xs invariant_inv_xs_suffix invariant_inv_firstEven_still_in_suffix_if_not_found invariant_inv_firstOdd_still_in_suffix_if_not_found invariant_inv_firstEven_is_global_first invariant_inv_firstOdd_is_global_first if_pos i i_1 i_2 if_pos_1 if_pos_2 invariant_inv_even_still_in_suffix invariant_inv_odd_still_in_suffix if_neg)
  exact (goal_7 lst require_1 firstEven firstOdd foundEven foundOdd xs invariant_inv_xs_suffix invariant_inv_firstEven_still_in_suffix_if_not_found invariant_inv_firstOdd_still_in_suffix_if_not_found invariant_inv_firstEven_is_global_first invariant_inv_firstOdd_is_global_first if_pos i i_1 i_2 if_pos_1 invariant_inv_even_still_in_suffix invariant_inv_odd_still_in_suffix if_neg if_neg_1)
  exact (goal_8 lst require_1)
  exact (goal_9 lst require_1)
  exact (goal_10 lst require_1)
  exact (goal_11 lst require_1 firstEven firstOdd foundEven foundOdd xs invariant_inv_xs_suffix invariant_inv_firstEven_still_in_suffix_if_not_found invariant_inv_firstOdd_still_in_suffix_if_not_found invariant_inv_firstEven_is_global_first invariant_inv_firstOdd_is_global_first a a_1 i i_1 i_2 i_3 xs_1 invariant_inv_even_still_in_suffix invariant_inv_odd_still_in_suffix i_4)
end Proof
