import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isPeakValley: Determine if a list of integers follows a peak-valley pattern
    Natural language breakdown:
    1. A list follows the peak-valley pattern if it strictly increases first, then strictly decreases
    2. Both the increasing part and decreasing part must be non-empty
    3. This means there must be a peak index k where:
       - All elements before k are strictly increasing (indices 0 to k)
       - All elements after k are strictly decreasing (indices k to end)
    4. The list must have at least 3 elements (at least one element in increasing part before peak,
       the peak itself, and at least one element in decreasing part after peak)
    5. No consecutive equal elements are allowed (must be strictly increasing then strictly decreasing)
    6. Examples:
       - [1, 3, 5, 4, 2] -> true (increases: 1<3<5, decreases: 5>4>2)
       - [1, 2, 3] -> false (only increasing, no decreasing part)
       - [5, 4, 3] -> false (only decreasing, no increasing part)
       - [1, 2, 2, 1] -> false (contains equal consecutive elements)
-/

section Specs
-- Helper: Check if a portion of a list is strictly increasing (from index i to j inclusive)
def isStrictlyIncreasingRange (lst : List Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < lst.length ∧ ∀ k : Nat, i ≤ k → k < j → lst[k]! < lst[k + 1]!

-- Helper: Check if a portion of a list is strictly decreasing (from index i to j inclusive)
def isStrictlyDecreasingRange (lst : List Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < lst.length ∧ ∀ k : Nat, i ≤ k → k < j → lst[k]! > lst[k + 1]!

-- Helper: Check if there exists a valid peak index
def hasPeakValleyStructure (lst : List Int) : Prop :=
  ∃ peakIdx : Nat,
    peakIdx > 0 ∧
    peakIdx < lst.length - 1 ∧
    isStrictlyIncreasingRange lst 0 peakIdx ∧
    isStrictlyDecreasingRange lst peakIdx (lst.length - 1)

def precondition (lst : List Int) :=
  True  -- no preconditions

def postcondition (lst : List Int) (result : Bool) :=
  result = true ↔ hasPeakValleyStructure lst
end Specs

section Impl
method isPeakValley (lst : List Int)
  return (result : Bool)
  require precondition lst
  ensures postcondition lst result
  do
  -- Need at least 3 elements for a valid peak-valley
  if lst.length < 3 then
    return false
  else
    let arr := lst.toArray
    let mut i : Nat := 0

    -- Find the peak: traverse while strictly increasing
    while i + 1 < arr.size ∧ arr[i]! < arr[i + 1]!
      -- i stays within bounds
      invariant "i_bound" i < arr.size
      -- array size equals list length
      invariant "size_eq" arr.size = lst.length
      -- array data equals list
      invariant "arr_eq_lst" arr.toList = lst
      -- size is at least 3
      invariant "size_ge_3" arr.size >= 3
      -- all elements from 0 to i-1 are strictly increasing
      invariant "increasing_prefix" ∀ k : Nat, k < i → arr[k]! < arr[k + 1]!
      done_with (i + 1 >= arr.size ∨ arr[i]! >= arr[i + 1]!)
    do
      i := i + 1

    -- Peak must be at a valid position (not at start, not at end)
    -- i is now the peak index
    if i = 0 then
      -- No increasing part
      return false
    else
      if i >= arr.size - 1 then
        -- Peak is at end, no decreasing part
        return false
      else
        -- Check that the rest is strictly decreasing
        let peakIdx := i
        let mut j := peakIdx
        let mut validDecrease := true

        while j + 1 < arr.size ∧ validDecrease
          -- j stays within bounds and >= peakIdx
          invariant "j_ge_peak" peakIdx ≤ j
          invariant "j_bound" j < arr.size
          -- array properties preserved
          invariant "size_eq2" arr.size = lst.length
          invariant "arr_eq_lst2" arr.toList = lst
          invariant "size_ge_3_2" arr.size >= 3
          -- peakIdx properties
          invariant "peak_bound_low" peakIdx > 0
          invariant "peak_bound_high" peakIdx < arr.size - 1
          invariant "peak_eq_i" peakIdx = i
          -- increasing part still valid
          invariant "increasing_part" ∀ k : Nat, k < peakIdx → arr[k]! < arr[k + 1]!
          -- if validDecrease, then decreasing from peakIdx to j
          invariant "decreasing_part" validDecrease = true → (∀ k : Nat, peakIdx ≤ k → k < j → arr[k]! > arr[k + 1]!)
          -- if validDecrease is false, there exists a violation of decreasing property
          invariant "no_structure_if_false" validDecrease = false → (∃ k : Nat, peakIdx ≤ k ∧ k < arr.size - 1 ∧ arr[k]! ≤ arr[k + 1]!)
          -- When validDecrease is true and we've checked up to j, track progress
          invariant "progress" validDecrease = true → j ≤ arr.size - 1
          done_with (j + 1 >= arr.size ∨ validDecrease = false)
        do
          if arr[j]! > arr[j + 1]! then
            j := j + 1
          else
            validDecrease := false

        -- validDecrease is true only if we went through the entire decreasing part
        return validDecrease
end Impl

section TestCases
-- Test case 1: Basic peak-valley pattern (from problem examples)
def test1_lst : List Int := [1, 3, 5, 2, 1]
def test1_Expected : Bool := true

-- Test case 2: Only increasing, no decreasing part
def test2_lst : List Int := [1, 2, 3, 4, 5]
def test2_Expected : Bool := false

-- Test case 3: Empty list
def test3_lst : List Int := []
def test3_Expected : Bool := false

-- Test case 4: Single element
def test4_lst : List Int := [1]
def test4_Expected : Bool := false

-- Test case 5: All equal elements (no strict increase/decrease)
def test5_lst : List Int := [1, 1, 1, 1, 1]
def test5_Expected : Bool := false

-- Test case 6: Valid peak-valley with large jump
def test6_lst : List Int := [1, 10, 100, 1]
def test6_Expected : Bool := true

-- Test case 7: Only decreasing, no increasing part
def test7_lst : List Int := [5, 4, 3, 2, 1]
def test7_Expected : Bool := false

-- Test case 8: Two elements (cannot have both increasing and decreasing parts)
def test8_lst : List Int := [1, 2]
def test8_Expected : Bool := false

-- Test case 9: Three elements forming valid peak
def test9_lst : List Int := [1, 3, 2]
def test9_Expected : Bool := true

-- Test case 10: Has equal consecutive elements (from problem examples)
def test10_lst : List Int := [1, 2, 2, 1]
def test10_Expected : Bool := false

-- Recommend to validate: 1, 6, 9
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((isPeakValley test1_lst).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isPeakValley test2_lst).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isPeakValley test3_lst).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isPeakValley test4_lst).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isPeakValley test5_lst).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isPeakValley test6_lst).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isPeakValley test7_lst).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isPeakValley test8_lst).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isPeakValley test9_lst).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((isPeakValley test10_lst).run), DivM.res test10_Expected ]
end Assertions

section Pbt
extract_program_for isPeakValley
prove_precondition_decidable_for isPeakValley
prove_postcondition_decidable_for isPeakValley
derive_tester_for isPeakValley
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (List Int)
    let res := isPeakValleyTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break

end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isPeakValley by
  -- loom_solve <;> (try simp at *; expose_names)


prove_correct isPeakValley by
  loom_solve_async <;> (try simp at *; expose_names)
end Proof
