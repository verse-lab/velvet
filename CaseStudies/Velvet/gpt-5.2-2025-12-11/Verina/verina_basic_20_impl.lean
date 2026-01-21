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
    uniqueProduct: product of all distinct integers in an array
    Natural language breakdown:
    1. Input is an array of integers.
    2. Consider the set of distinct integer values that occur in the array.
    3. Multiply each distinct value exactly once; order does not matter.
    4. If the array is empty, there are no distinct values, so the product is 1.
    5. Duplicates in the array do not change the result.
    6. Zero is handled normally: if 0 occurs in the array, the unique-product is 0.
-/

section Specs
-- Helper: the finset of values appearing in the array (deduplicated).
-- We use Mathlib's List.toFinset to represent distinct elements.

def distinctVals (arr : Array Int) : Finset Int :=
  arr.toList.toFinset

-- Helper: product over the distinct values (order-independent).
-- Finset.prod uses commutative multiplication on Int with identity 1.

def distinctProduct (arr : Array Int) : Int :=
  (distinctVals arr).prod (fun x => x)

-- No preconditions.

def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: result equals the product of all distinct values in the array.
-- This captures: empty array -> product over empty finset -> 1.

def postcondition (arr : Array Int) (result : Int) : Prop :=
  result = distinctProduct arr
end Specs

section Impl
method uniqueProduct (arr : Array Int) return (result : Int)
  require precondition arr
  ensures postcondition arr result
  do
  -- We compute the product of distinct values by scanning the array,
  -- keeping a growing array of "seen" values.
  let mut seen : Array Int := #[]
  let mut prod : Int := 1
  let mut i : Nat := 0

  while i < arr.size
    -- Invariant: index i stays within bounds.
    -- Init: i=0. Preserved: i increments by 1.
    invariant "inv_outer_bounds" i ≤ arr.size
    -- Invariant: the accumulator matches the product over the distinct values in `seen`.
    -- Init: prod=1 and distinctProduct #[] = 1. Preserved: when we push a new value, we
    -- update prod accordingly; when already=true, neither prod nor seen changes.
    invariant "inv_outer_prod" prod = distinctProduct seen
    -- Invariant: no duplicates in `seen` (so pushing when fresh behaves like Finset.insert).
    -- Init: empty array has no duplicates. Preserved: we only push when x is not in seen.
    invariant "inv_outer_seen_nodup" seen.toList.Nodup
  do
    let x := arr[i]!

    -- Check whether x has been seen before.
    let mut j : Nat := 0
    let mut already : Bool := false
    while j < seen.size
      -- Invariant: inner index j stays within bounds.
      invariant "inv_inner_bounds" j ≤ seen.size
      -- Invariant: if already=false, then x is not equal to any element scanned so far.
      -- Init: j=0 vacuous. Preserved by increment when the comparison fails.
      invariant "inv_inner_notseen_prefix" (already = false → ∀ k, k < j → seen[k]! ≠ x)
      -- Invariant: if already=true, we have found a witness index < j where seen[index]=x.
      -- This lets the outer loop deduce x ∈ distinctVals seen on the already=true path.
      invariant "inv_inner_found_witness" (already = true → ∃ k, k < j ∧ seen[k]! = x)
      done_with (j = seen.size ∨ already = true)
    do
      if seen[j]! = x then
        already := true
        break
      j := j + 1

    if already = false then
      prod := prod * x
      seen := seen.push x

    i := i + 1

  return prod
end Impl

section TestCases
-- Test case 1: example from prompt
-- distinct values {2,3,4} -> 2*3*4 = 24

def test1_arr : Array Int := #[2, 3, 2, 4]

def test1_Expected : Int := 24

-- Test case 2: all elements same

def test2_arr : Array Int := #[5, 5, 5, 5]

def test2_Expected : Int := 5

-- Test case 3: empty array -> 1

def test3_arr : Array Int := #[]

def test3_Expected : Int := 1

-- Test case 4: already unique

def test4_arr : Array Int := #[1, 2, 3]

def test4_Expected : Int := 6

-- Test case 5: contains zero -> product is zero

def test5_arr : Array Int := #[0, 2, 3]

def test5_Expected : Int := 0

-- Test case 6: negative numbers with duplicates
-- distinct values {-1,-2,-3} -> (-1)*(-2)*(-3) = -6

def test6_arr : Array Int := #[-1, -2, -1, -3]

def test6_Expected : Int := -6

-- Test case 7: larger positive values with duplicates
-- distinct values {10,20,30} -> 6000

def test7_arr : Array Int := #[10, 10, 20, 20, 30]

def test7_Expected : Int := 6000

-- Test case 8: mixture with sign and duplicates
-- distinct values {-2,0,2} -> 0

def test8_arr : Array Int := #[-2, 0, 2, -2, 2]

def test8_Expected : Int := 0

-- Test case 9: single element

def test9_arr : Array Int := #[7]

def test9_Expected : Int := 7

-- Recommend to validate: 1, 3, 6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((uniqueProduct test1_arr).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((uniqueProduct test2_arr).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((uniqueProduct test3_arr).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((uniqueProduct test4_arr).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((uniqueProduct test5_arr).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((uniqueProduct test6_arr).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((uniqueProduct test7_arr).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((uniqueProduct test8_arr).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((uniqueProduct test9_arr).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for uniqueProduct
prove_precondition_decidable_for uniqueProduct
prove_postcondition_decidable_for uniqueProduct
derive_tester_for uniqueProduct
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := uniqueProductTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct uniqueProduct by
  -- loom_solve <;> (try simp at *; expose_names)
end Proof
