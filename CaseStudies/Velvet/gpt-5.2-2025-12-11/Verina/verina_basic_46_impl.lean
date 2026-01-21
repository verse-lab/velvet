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
    lastPosition: find the last occurrence of an element in a sorted array of integers.
    Natural language breakdown:
    1. Input is an array `arr : Array Int` and an integer `elem : Int`.
    2. The array is assumed to be sorted in non-decreasing order.
    3. The method returns an integer index `result`.
    4. If `elem` occurs in the array, `result` is the greatest index (0-based) where `arr[result] = elem`.
    5. If `elem` does not occur in the array, the method returns -1.
    6. If `result` is not -1, it must be a valid index: 0 ≤ result < arr.size.
    7. All indices strictly larger than `result` (but still in bounds) must not contain `elem`.
    8. The input array is not modified by the method.
-/

section Specs
-- Helper: array sorted in non-decreasing order (by Nat indices)
def isSortedNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: element occurs in array
def occurs (arr : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

-- Helper: no occurrence of element in array
def notOccurs (arr : Array Int) (x : Int) : Prop :=
  ∀ (i : Nat), i < arr.size → arr[i]! ≠ x

-- Helper: an Int is a valid in-bounds array index
-- Note: we relate the Int index to Nat bounds via Int.toNat.
def isValidIndexInt (arr : Array Int) (idx : Int) : Prop :=
  0 ≤ idx ∧ Int.toNat idx < arr.size

-- Helper: map an Int index to a Nat index (used only when in-bounds)
def idxNat (idx : Int) : Nat :=
  Int.toNat idx

-- Preconditions
-- The only required assumption is sortedness (rejects unsorted inputs like #[3,2,1]).
def precondition (arr : Array Int) (elem : Int) : Prop :=
  isSortedNondecreasing arr

-- Postconditions
-- If present: result is the last index containing elem.
-- If absent: result is -1.
def postcondition (arr : Array Int) (elem : Int) (result : Int) : Prop :=
  (result = (-1) ∧ notOccurs arr elem) ∨
  (isValidIndexInt arr result ∧
    arr[idxNat result]! = elem ∧
    (∀ (j : Nat), idxNat result < j → j < arr.size → arr[j]! ≠ elem) ∧
    (∀ (i : Nat), i < arr.size → arr[i]! = elem → i ≤ idxNat result))
end Specs

section Impl
method lastPosition (arr : Array Int) (elem : Int)
  return (result : Int)
  require precondition arr elem
  ensures postcondition arr elem result
  do
    let mut i : Nat := 0
    let mut found : Bool := false
    let mut last : Nat := 0

    while i < arr.size
      -- i stays within bounds; needed for safe array access and termination.
      invariant "lp_i_bounds" i ≤ arr.size
      -- found precisely tracks whether elem occurs in the prefix [0, i).
      -- Init: i=0, found=false and no index <0 exists. Preserve: update found when seeing elem.
      invariant "lp_found_iff_prefix_occurs" (found = true ↔ ∃ j : Nat, j < i ∧ arr[j]! = elem)
      -- When found, last is a valid index within the processed prefix and points to elem.
      -- Init: found=false so vacuous. Preserve: last updated to current i when elem seen.
      invariant "lp_last_points_to_elem" (found = true → last < i ∧ arr[last]! = elem)
      -- last is the last occurrence within the processed prefix: no elem appears after last and before i.
      -- Init: vacuous. Preserve: when last updated to i, the interval is empty; otherwise i increases and the new point is checked.
      invariant "lp_last_is_last_in_prefix" (found = true → ∀ j : Nat, last < j → j < i → arr[j]! ≠ elem)
      done_with i = arr.size
    do
      if arr[i]! = elem then
        found := true
        last := i
      i := i + 1

    if found then
      return (Int.ofNat last)
    else
      return (-1)
end Impl

section TestCases
-- Test case 1: example from prompt, element appears multiple times
-- arr = #[1,2,2,3,4,5], elem = 2, last index = 2
def test1_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test1_elem : Int := 2
def test1_Expected : Int := 2

-- Test case 2: example, element absent
def test2_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test2_elem : Int := 6
def test2_Expected : Int := -1

-- Test case 3: example, element is the last element
def test3_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test3_elem : Int := 5
def test3_Expected : Int := 5

-- Test case 4: example, single element present
def test4_arr : Array Int := #[1]
def test4_elem : Int := 1
def test4_Expected : Int := 0

-- Test case 5: example, all elements equal to elem
def test5_arr : Array Int := #[1, 1, 1, 1]
def test5_elem : Int := 1
def test5_Expected : Int := 3

-- Test case 6: example, duplicates at end
def test6_arr : Array Int := #[2, 2, 3, 3, 3]
def test6_elem : Int := 3
def test6_Expected : Int := 4

-- Test case 7: empty array (sorted), element absent
def test7_arr : Array Int := #[]
def test7_elem : Int := 10
def test7_Expected : Int := -1

-- Test case 8: sorted array with negative values and duplicates
def test8_arr : Array Int := #[-3, -1, -1, 0, 7]
def test8_elem : Int := -1
def test8_Expected : Int := 2

-- Test case 9: sorted array, element smaller than all values (absent)
def test9_arr : Array Int := #[0, 1, 2, 3]
def test9_elem : Int := -5
def test9_Expected : Int := -1

-- Recommend to validate: 1, 4, 8
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((lastPosition test1_arr test1_elem).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((lastPosition test2_arr test2_elem).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((lastPosition test3_arr test3_elem).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((lastPosition test4_arr test4_elem).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((lastPosition test5_arr test5_elem).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((lastPosition test6_arr test6_elem).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((lastPosition test7_arr test7_elem).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((lastPosition test8_arr test8_elem).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((lastPosition test9_arr test9_elem).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for lastPosition
prove_precondition_decidable_for lastPosition
prove_postcondition_decidable_for lastPosition
derive_tester_for lastPosition
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Int)
    let res := lastPositionTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct lastPosition by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (arr : Array ℤ)
    (elem : ℤ)
    (found : Bool)
    (i : ℕ)
    (last : ℕ)
    (invariant_lp_last_points_to_elem : found = true → last < i ∧ arr[last]! = elem)
    (invariant_lp_last_is_last_in_prefix : found = true → ∀ (j : ℕ), last < j → j < i → ¬arr[j]! = elem)
    (done_1 : i = arr.size)
    (i_1 : Bool)
    (i_2 : ℕ)
    (last_1 : ℕ)
    (if_pos : i_1 = true)
    (i_3 : found = i_1 ∧ i = i_2 ∧ last = last_1)
    : postcondition arr elem ↑last_1 := by
    -- Move `found = true` back to original `found`
    have hfound : found = true := by
      calc
        found = i_1 := i_3.1
        _ = true := if_pos

    -- Get `last < i` and `arr[last]! = elem`, then rewrite to `last_1`
    have hlast_lt_i : last < i := (invariant_lp_last_points_to_elem hfound).1
    have hlast_eq_elem : arr[last]! = elem := (invariant_lp_last_points_to_elem hfound).2

    have hi : i = arr.size := done_1
    have hlast : last = last_1 := i_3.2.2

    have hlast1_lt_size : last_1 < arr.size := by
      have : last < arr.size := by simpa [hi] using hlast_lt_i
      simpa [hlast] using this

    have hlast1_eq_elem : arr[last_1]! = elem := by
      simpa [hlast] using hlast_eq_elem

    -- "No elem after last_1"
    have hno_after_last1 : ∀ (j : ℕ), last_1 < j → j < arr.size → ¬arr[j]! = elem := by
      intro j hj1 hj2
      have hno := invariant_lp_last_is_last_in_prefix hfound j
      -- convert bounds via rewriting `last = last_1` and `i = arr.size`
      have : ¬arr[j]! = elem := by
        apply hno
        · -- last < j
          simpa [hlast] using hj1
        · -- j < i
          simpa [hi] using hj2
      simpa using this

    -- Any occurrence index is ≤ last_1 (otherwise contradict hno_after_last1)
    have hmax_last1 : ∀ (k : ℕ), k < arr.size → arr[k]! = elem → k ≤ last_1 := by
      intro k hk hkeq
      by_contra hnot
      have hlt : last_1 < k := Nat.lt_of_not_ge hnot
      have : ¬arr[k]! = elem := hno_after_last1 k hlt hk
      exact this hkeq

    -- Build postcondition: second disjunct
    right
    constructor
    · -- isValidIndexInt arr (↑last_1)
      constructor
      · -- 0 ≤ (↑last_1)
        simpa using (Int.ofNat_nonneg last_1)
      · -- Int.toNat (↑last_1) < arr.size
        simpa using hlast1_lt_size
    · constructor
      · -- arr[idxNat ↑last_1]! = elem
        simpa [idxNat] using hlast1_eq_elem
      · constructor
        · -- no elem occurs after idxNat ↑last_1
          simpa [idxNat] using hno_after_last1
        · -- every occurrence is ≤ idxNat ↑last_1
          intro k hk hkeq
          simpa [idxNat] using (hmax_last1 k hk hkeq)

theorem goal_1
    (arr : Array ℤ)
    (elem : ℤ)
    (found : Bool)
    (i : ℕ)
    (last : ℕ)
    (invariant_lp_found_iff_prefix_occurs : found = true ↔ ∃ j < i, arr[j]! = elem)
    (done_1 : i = arr.size)
    (i_1 : Bool)
    (i_2 : ℕ)
    (last_1 : ℕ)
    (i_3 : found = i_1 ∧ i = i_2 ∧ last = last_1)
    (if_neg : i_1 = false)
    : postcondition arr elem (-1) := by
    left
    constructor
    · rfl
    · -- prove `notOccurs arr elem`
      unfold notOccurs
      intro k hk
      -- get `found = false`, hence `¬ found = true`
      have hnotFoundTrue : ¬ found = true := by
        have hfoundFalse : found = false := by
          calc
            found = i_1 := i_3.1
            _ = false := if_neg
        -- rewrite with `hfoundFalse`
        simpa [hfoundFalse]
      -- from invariant, derive no occurrence in the (full) array
      have hnoPrefix : ¬ (∃ j < i, arr[j]! = elem) :=
        (not_congr invariant_lp_found_iff_prefix_occurs).1 hnotFoundTrue
      have hnoAll : ¬ (∃ j < arr.size, arr[j]! = elem) := by
        simpa [done_1] using hnoPrefix
      intro hkEq
      apply hnoAll
      exact ⟨k, hk, hkEq⟩


prove_correct lastPosition by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 arr elem found i last invariant_lp_last_points_to_elem invariant_lp_last_is_last_in_prefix done_1 i_1 i_2 last_1 if_pos i_3)
  exact (goal_1 arr elem found i last invariant_lp_found_iff_prefix_occurs done_1 i_1 i_2 last_1 i_3 if_neg)
end Proof
