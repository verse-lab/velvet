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
    BubbleSort: Sort an array of integers in non-decreasing order, preserving the multiset of elements.
    Natural language breakdown:
    1. Input is an array of integers; it may be empty or non-empty.
    2. Output is an array of integers with the same size as the input.
    3. Output is sorted in non-decreasing order: for any indices i < j within bounds,
       output[i]! ≤ output[j]!. 
    4. Output is a rearrangement (permutation) of the input: it contains exactly the same elements
       with the same multiplicities (multiset/bag of elements is preserved).
    5. No special preconditions are required; the function must handle all arrays.
-/

section Specs
-- Helper: array sortedness in non-decreasing order (index-based, using safe access `a[i]!`).
-- This is the direct requirement from the prompt.
def arraySorted (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

-- Helper: multiset preservation encoded via List permutation.
-- `List.Perm` is in Mathlib and avoids needing `List.toMultiset`.
def arrayPerm (a : Array Int) (b : Array Int) : Prop :=
  a.toList.Perm b.toList

-- No preconditions.
def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  arraySorted result ∧
  arrayPerm a result
end Specs

section Impl
method BubbleSort (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
    let mut arr := a
    let mut n : Nat := arr.size

    -- Standard bubble sort (in-place via functional array updates)
    while (0 < n)
      -- Invariant: n is always within bounds of the (fixed-size) array.
      -- Init: n = arr.size. Preserved by n := n - 1 since Nat.sub_le.
      invariant "bs_outer_n_bounds" n ≤ arr.size
      -- Invariant: swaps preserve array size, so arr.size stays equal to the original input size.
      -- Init: arr = a. Preserved by elemSwap!_size.
      invariant "bs_outer_size_preserved" arr.size = a.size
      -- Invariant: adjacent swaps preserve permutation of the original list.
      -- Init: Perm.refl. Preserved by permutation lemma for swaps.
      invariant "bs_outer_perm" arrayPerm a arr
      -- Invariant: the suffix starting at index n is already sorted among itself.
      -- This is preserved by the inner loop because swaps only touch indices < n.
      invariant "bs_outer_suffix_sorted_from_n" (∀ i j, n ≤ i → i < j → j < arr.size → arr[i]! ≤ arr[j]!)
      done_with (n = 0)
    do
      let mut i : Nat := 0
      while (i + 1 < n)
        -- Invariant: i stays within the current prefix boundary n.
        -- Init: i = 0. Preserved by i := i + 1.
        invariant "bs_inner_i_le" i ≤ n
        -- Invariant: i+1 is within array bounds, so arr[i]! and arr[i+1]! are safe.
        -- Follows from i+1 < n and n ≤ arr.size.
        invariant "bs_inner_i1_le_size" i + 1 ≤ arr.size
        -- Invariant: propagate outer facts.
        invariant "bs_inner_n_bounds" n ≤ arr.size
        invariant "bs_inner_size_preserved" arr.size = a.size
        invariant "bs_inner_perm" arrayPerm a arr
        -- Invariant: keep the already-sorted suffix starting at n.
        invariant "bs_inner_suffix_sorted_from_n" (∀ p q, n ≤ p → p < q → q < arr.size → arr[p]! ≤ arr[q]!)
        done_with (i + 1 >= n)
      do
        if arr[i]! > arr[i + 1]! then
          arr := elemSwap! arr i (i + 1)
        i := i + 1
      n := n - 1

    return arr
end Impl

section TestCases
-- Test case 1: example from prompt (reverse sorted)
def test1_a : Array Int := #[5, 4, 3, 2, 1]
def test1_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 2: already sorted
def test2_a : Array Int := #[1, 2, 3, 4, 5]
def test2_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 3: duplicates and unsorted
def test3_a : Array Int := #[3, 1, 2, 1, 5]
def test3_Expected : Array Int := #[1, 1, 2, 3, 5]

-- Test case 4: singleton
def test4_a : Array Int := #[10]
def test4_Expected : Array Int := #[10]

-- Test case 5: multiple duplicates
def test5_a : Array Int := #[4, 4, 4, 2, 2, 8]
def test5_Expected : Array Int := #[2, 2, 4, 4, 4, 8]

-- Test case 6: empty array
def test6_a : Array Int := #[]
def test6_Expected : Array Int := #[]

-- Test case 7: contains negative and positive values
def test7_a : Array Int := #[-2, 0, 5, -1]
def test7_Expected : Array Int := #[-2, -1, 0, 5]

-- Test case 8: all elements equal
def test8_a : Array Int := #[7, 7, 7]
def test8_Expected : Array Int := #[7, 7, 7]

-- Test case 9: two elements swapped
def test9_a : Array Int := #[2, 1]
def test9_Expected : Array Int := #[1, 2]

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 3, 7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((BubbleSort test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((BubbleSort test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((BubbleSort test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((BubbleSort test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((BubbleSort test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((BubbleSort test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((BubbleSort test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((BubbleSort test8_a).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((BubbleSort test9_a).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for BubbleSort
prove_precondition_decidable_for BubbleSort
prove_postcondition_decidable_for BubbleSort
derive_tester_for BubbleSort
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := BubbleSortTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct BubbleSort by
  -- loom_solve <;> (try simp at *; expose_names)
end Proof
