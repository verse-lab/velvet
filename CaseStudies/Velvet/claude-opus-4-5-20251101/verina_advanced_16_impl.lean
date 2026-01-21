import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    insertionSort: Sort a list of integers using insertion sort algorithm
    Natural language breakdown:
    1. We have an input list of integers
    2. The output must be a sorted list in ascending order
    3. The output must be a permutation of the input (contain exactly the same elements)
    4. The algorithm should follow insertion sort approach (placing each element in correct position)
    5. Edge cases: empty list returns empty list, single element list returns itself
    6. Duplicate elements should be preserved
    7. Negative numbers should be handled correctly
-/

section Specs
-- Helper function to check if a list is sorted in ascending order
-- Using List.Sorted from Mathlib with (· ≤ ·) relation
def isSortedAsc (xs : List Int) : Prop :=
  List.Sorted (· ≤ ·) xs

-- Helper function to check if two lists are permutations of each other
-- Using List.Perm from Mathlib (explicit form instead of ~ notation)
def isPermOf (xs : List Int) (ys : List Int) : Prop :=
  List.Perm xs ys

-- Precondition: no constraints on input
def precondition (xs : List Int) : Prop :=
  True

-- Postcondition: result is sorted and is a permutation of input
def postcondition (xs : List Int) (result : List Int) : Prop :=
  isSortedAsc result ∧ isPermOf result xs
end Specs

section Impl
method insertionSort (xs : List Int)
  return (result : List Int)
  require precondition xs
  ensures postcondition xs result
  do
  let mut arr := xs.toArray
  let mut i := 1
  while i < arr.size
    -- Invariant 1: i is bounded properly
    invariant "i_lower_bound" 1 ≤ i
    invariant "i_upper_bound" arr.size = 0 ∨ i ≤ arr.size
    -- Invariant 2: array size is preserved
    invariant "size_preserved" arr.size = xs.length
    -- Invariant 3: array is a permutation of original
    invariant "is_perm" List.Perm arr.toList xs
    -- Invariant 4: prefix arr[0..i] is sorted
    invariant "prefix_sorted" List.Sorted (· ≤ ·) (arr.toList.take i)
    done_with i >= arr.size
  do
    let key := arr[i]!
    let mut j := i
    while j > 0 ∧ arr[j - 1]! > key
      -- Inner loop bounds
      invariant "j_lower" 0 ≤ j
      invariant "j_upper" j ≤ i
      invariant "i_in_bounds" i < arr.size
      -- Size preservation through inner loop
      invariant "inner_size" arr.size = xs.length
      -- Outer loop index bound preserved
      invariant "outer_i_bound" 1 ≤ i
      -- Track that inserting key at position j restores the permutation
      invariant "inner_perm_with_key" List.Perm ((arr.toList.take j) ++ [key] ++ (arr.toList.drop (j + 1))) xs
      -- Prefix up to j is unchanged and sorted
      invariant "prefix_unchanged_sorted" List.Sorted (· ≤ ·) (arr.toList.take j)
      -- Elements in positions j..i are all > key (these are the shifted elements)
      invariant "shifted_greater" ∀ k, j < k ∧ k ≤ i → arr[k]! > key
      -- Elements from j to i match their sorted order from original prefix
      invariant "shifted_from_sorted" ∀ k₁ k₂, j ≤ k₁ ∧ k₁ < k₂ ∧ k₂ ≤ i → arr[k₁]! ≤ arr[k₂]!
      done_with j <= 0 ∨ arr[j - 1]! <= key
    do
      arr := arr.set! j (arr[j - 1]!)
      j := j - 1
    arr := arr.set! j key
    i := i + 1
  return arr.toList
end Impl

section TestCases
-- Test case 1: Example from problem description
def test1_xs : List Int := [3, 1, 4, 2]
def test1_Expected : List Int := [1, 2, 3, 4]

-- Test case 2: Empty list
def test2_xs : List Int := []
def test2_Expected : List Int := []

-- Test case 3: Single element
def test3_xs : List Int := [42]
def test3_Expected : List Int := [42]

-- Test case 4: List with negative numbers and duplicates
def test4_xs : List Int := [5, -1, 0, 10, -1]
def test4_Expected : List Int := [-1, -1, 0, 5, 10]

-- Test case 5: All elements are the same
def test5_xs : List Int := [2, 2, 2, 2, 2]
def test5_Expected : List Int := [2, 2, 2, 2, 2]

-- Test case 6: Already sorted list
def test6_xs : List Int := [1, 2, 3, 4, 5]
def test6_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 7: Reverse sorted list
def test7_xs : List Int := [5, 4, 3, 2, 1]
def test7_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 8: List with two elements
def test8_xs : List Int := [7, 3]
def test8_Expected : List Int := [3, 7]

-- Recommend to validate: 1, 2, 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((insertionSort test1_xs).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((insertionSort test2_xs).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((insertionSort test3_xs).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((insertionSort test4_xs).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((insertionSort test5_xs).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((insertionSort test6_xs).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((insertionSort test7_xs).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((insertionSort test8_xs).run), DivM.res test8_Expected ]
end Assertions

section Pbt
extract_program_for insertionSort
prove_precondition_decidable_for insertionSort
prove_postcondition_decidable_for insertionSort
derive_tester_for insertionSort
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (List Int)
    let res := insertionSortTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct insertionSort by
  -- loom_solve <;> (try simp at *; expose_names)


prove_correct insertionSort by
  loom_solve <;> (try simp at *; expose_names)
end Proof
