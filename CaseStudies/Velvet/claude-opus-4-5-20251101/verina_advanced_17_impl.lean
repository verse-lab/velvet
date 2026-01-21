import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- insertionSort: Sort a list of integers in ascending order using insertion sort
--
-- Natural language breakdown:
-- 1. The input is a list of integers that may be in any order
-- 2. The output must be a sorted list in non-decreasing order (ascending)
-- 3. The output must be a permutation of the input (same elements, possibly reordered)
-- 4. Sorted means: for all adjacent elements, the earlier one is ≤ the later one
-- 5. Permutation means: the output contains exactly the same elements with the same multiplicities
-- 6. We use List.Sorted from Mathlib which defines sortedness via Pairwise relation
-- 7. We use List.Perm from Lean/Mathlib to express permutation property

section Specs
-- Precondition: No restrictions on input list
def precondition (l : List Int) : Prop :=
  True

-- Postcondition: Result is sorted and is a permutation of input
-- Using Mathlib's List.Sorted for sortedness property
-- Using List.Perm for permutation property
def postcondition (l : List Int) (result : List Int) : Prop :=
  List.Sorted (· ≤ ·) result ∧ List.Perm l result
end Specs

section Impl
method insertionSort (l : List Int)
  return (result : List Int)
  require precondition l
  ensures postcondition l result
  do
  -- Convert list to array for imperative manipulation
  let mut arr := l.toArray
  let mut i := 1
  -- Outer loop: iterate through each element starting from index 1
  while i < arr.size
    -- i starts at 1 and increases; when arr is empty, loop doesn't execute
    invariant "i_lower" 1 ≤ i
    -- i is bounded by array size (only relevant when loop executes)
    invariant "i_upper" i ≤ arr.size ∨ arr.size = 0
    -- Array size is preserved
    invariant "size_preserved" arr.size = l.length
    -- Array is a permutation of the original list
    invariant "perm_preserved" List.Perm l arr.toList
    -- Elements arr[0..i) are sorted
    invariant "prefix_sorted" List.Sorted (· ≤ ·) (arr.toList.take i)
    done_with i = arr.size
  do
    -- Store the current element to insert
    let key := arr[i]!
    let mut j := i
    -- Inner loop: shift elements greater than key to the right
    while j > 0 ∧ arr[j-1]! > key
      -- j is bounded between 0 and i
      invariant "j_lower" 0 ≤ j
      invariant "j_upper" j ≤ i
      -- i is still bounded
      invariant "i_bound_inner" i < arr.size
      -- Array size preserved in inner loop
      invariant "size_inner" arr.size = l.length
      -- Permutation is restored when key is inserted at j
      invariant "perm_inner" List.Perm l (arr.toList.set j key)
      -- Prefix arr[0..j) remains sorted
      invariant "prefix_sorted_inner" List.Sorted (· ≤ ·) (arr.toList.take j)
      -- Elements from j+1 to i are all greater than key (shifted elements)
      invariant "shifted_greater" ∀ k, j < k ∧ k ≤ i → arr[k]! > key
      -- Elements from j to i are sorted (shifted from original sorted prefix)
      invariant "suffix_sorted" List.Sorted (· ≤ ·) ((arr.toList.drop j).take (i - j + 1))
      -- Connection: if j < i then arr[j]! ≤ arr[j+1]! (maintains sorted order in shifted region)
      invariant "connection" j < i → arr[j]! ≤ arr[j+1]!
      done_with j = 0 ∨ arr[j-1]! ≤ key
    do
      arr := arr.set! j (arr[j-1]!)
      j := j - 1
    -- Insert the key at the correct position
    arr := arr.set! j key
    i := i + 1
  return arr.toList
end Impl

section TestCases
-- Test case 1: Empty list
def test1_l : List Int := []
def test1_Expected : List Int := []

-- Test case 2: Single element list
def test2_l : List Int := [5]
def test2_Expected : List Int := [5]

-- Test case 3: Already sorted list
def test3_l : List Int := [1, 2, 3]
def test3_Expected : List Int := [1, 2, 3]

-- Test case 4: Reverse sorted list
def test4_l : List Int := [3, 2, 1]
def test4_Expected : List Int := [1, 2, 3]

-- Test case 5: List with duplicates
def test5_l : List Int := [4, 2, 2, 3]
def test5_Expected : List Int := [2, 2, 3, 4]

-- Test case 6: List with negative numbers
def test6_l : List Int := [3, -1, 4, -5, 2]
def test6_Expected : List Int := [-5, -1, 2, 3, 4]

-- Test case 7: List with all same elements
def test7_l : List Int := [7, 7, 7, 7]
def test7_Expected : List Int := [7, 7, 7, 7]

-- Test case 8: Two elements in wrong order
def test8_l : List Int := [10, 5]
def test8_Expected : List Int := [5, 10]

-- Test case 9: Longer list with mixed values
def test9_l : List Int := [5, 2, 8, 1, 9, 3]
def test9_Expected : List Int := [1, 2, 3, 5, 8, 9]

-- Recommend to validate: 1, 4, 5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((insertionSort test1_l).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((insertionSort test2_l).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((insertionSort test3_l).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((insertionSort test4_l).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((insertionSort test5_l).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((insertionSort test6_l).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((insertionSort test7_l).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((insertionSort test8_l).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((insertionSort test9_l).run), DivM.res test9_Expected ]
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
