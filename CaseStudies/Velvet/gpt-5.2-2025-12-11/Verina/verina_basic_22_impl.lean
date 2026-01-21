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
    dissimilarElements: return the sorted array of all distinct integers that occur in exactly one of the two input arrays.
    Natural language breakdown:
    1. Inputs are two arrays of integers a and b.
    2. An integer x is considered part of the result iff it appears in a or b, but not in both.
    3. The output contains no duplicate elements.
    4. The output is sorted in nondecreasing order.
    5. The order is otherwise irrelevant (but since sortedness is required, the output order is uniquely determined up to duplicates, which are forbidden).
    6. There are no restrictions on input sizes or contents (may contain duplicates, negatives, or be empty).
-/

section Specs
-- Helper: membership predicate for an Int in an Array Int
-- Uses array indexing semantics via existence of an index.
def memArray (arr : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

-- Helper: output is sorted in nondecreasing order (Int ≤)
def arraySorted (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: no duplicates in an array
-- Stated via list nodup on the underlying list.
def arrayNodup (arr : Array Int) : Prop :=
  arr.toList.Nodup

-- The symmetric-difference membership condition for output array.
def symmDiffSpec (a : Array Int) (b : Array Int) (out : Array Int) : Prop :=
  ∀ (x : Int), memArray out x ↔ ((memArray a x ∧ ¬ memArray b x) ∨ (memArray b x ∧ ¬ memArray a x))

-- Preconditions: none

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- Postconditions: out contains exactly the symmetric difference elements, is duplicate-free, and sorted.
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  symmDiffSpec a b result ∧
  arrayNodup result ∧
  arraySorted result
end Specs

section Impl
method dissimilarElements (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  let mut out : Array Int := #[]

  -- local decidable membership check (computable)
  let mut i : Nat := 0
  while i < a.size
    -- Invariant: i stays within bounds of a (init i=0, preserved by i:=i+1)
    invariant "inv_a_loop_bounds" i ≤ a.size
    -- Invariant: out stays duplicate-free (only push when not already in out)
    invariant "inv_a_loop_nodup" arrayNodup out
    -- Invariant: soundness for out during first pass: out ⊆ a \ b
    invariant "inv_a_loop_out_sound" ∀ x : Int, memArray out x → (memArray a x ∧ ¬ memArray b x)
    -- Invariant: completeness for scanned prefix of a with element-wise membership
    -- We track membership via memArray a x (rather than direct indexing) so it is stable
    -- under later updates of i and can be re-established after each iteration.
    invariant "inv_a_loop_complete_prefix_mem"
      ∀ x : Int, (memArray a x ∧ ¬ memArray b x) → (∃ t : Nat, t < i ∧ a[t]! = x) → memArray out x
  do
    let x := a[i]!

    -- check if x is in b
    let mut inB : Bool := false
    let mut ib : Nat := 0
    while ib < b.size ∧ (inB = false)
      -- Invariant: ib stays within bounds
      invariant "inv_inB_bounds" ib ≤ b.size
      -- Invariant: if still not found, x is not in scanned prefix b[0..ib)
      invariant "inv_inB_nohit" (inB = false) → (∀ t : Nat, t < ib → b[t]! ≠ x)
      -- Invariant: if found, there is a witness in the scanned prefix
      invariant "inv_inB_hit_witness" (inB = true) → (∃ t : Nat, t < ib ∧ b[t]! = x)
      done_with (ib = b.size ∨ inB = true)
    do
      if b[ib]! = x then
        inB := true
      ib := ib + 1

    if inB then
      i := i + 1
      continue

    -- check if x already in out
    let mut inOut : Bool := false
    let mut io : Nat := 0
    while io < out.size ∧ (inOut = false)
      -- Invariant: io stays within bounds
      invariant "inv_inOut_bounds" io ≤ out.size
      -- Invariant: if still not found, x is not in scanned prefix out[0..io)
      invariant "inv_inOut_nohit" (inOut = false) → (∀ t : Nat, t < io → out[t]! ≠ x)
      -- Invariant: if found, there is a witness in the scanned prefix
      invariant "inv_inOut_hit_witness" (inOut = true) → (∃ t : Nat, t < io ∧ out[t]! = x)
      done_with (io = out.size ∨ inOut = true)
    do
      if out[io]! = x then
        inOut := true
      io := io + 1

    if inOut then
      i := i + 1
      continue

    out := out.push x
    i := i + 1

  let mut j : Nat := 0
  while j < b.size
    -- Invariant: j stays within bounds of b
    invariant "inv_b_loop_bounds" j ≤ b.size
    -- Invariant: out stays duplicate-free
    invariant "inv_b_loop_nodup" arrayNodup out
    -- Invariant: soundness for out during second pass: out ⊆ (a\b) ∪ (b\a)
    invariant "inv_b_loop_out_sound" ∀ x : Int, memArray out x → ((memArray a x ∧ ¬ memArray b x) ∨ (memArray b x ∧ ¬ memArray a x))
    -- Invariant: completeness for a-side is already established after first loop and preserved
    invariant "inv_b_loop_complete_a_side" ∀ x : Int, (memArray a x ∧ ¬ memArray b x) → memArray out x
    -- Invariant: completeness for scanned prefix of b: any b[t] (t<j) that is in b\a is in out
    -- This avoids the off-by-one issue by quantifying directly over indices < j.
    invariant "inv_b_loop_complete_b_prefix_idx"
      ∀ t : Nat, t < j → (¬ memArray a (b[t]!)) → memArray out (b[t]!)
  do
    let y := b[j]!

    -- check if y is in a
    let mut inA : Bool := false
    let mut ia : Nat := 0
    while ia < a.size ∧ (inA = false)
      -- Invariant: ia stays within bounds
      invariant "inv_inA_bounds" ia ≤ a.size
      -- Invariant: if still not found, y is not in scanned prefix a[0..ia)
      invariant "inv_inA_nohit" (inA = false) → (∀ t : Nat, t < ia → a[t]! ≠ y)
      -- Invariant: if found, there is a witness in the scanned prefix
      invariant "inv_inA_hit_witness" (inA = true) → (∃ t : Nat, t < ia ∧ a[t]! = y)
      done_with (ia = a.size ∨ inA = true)
    do
      if a[ia]! = y then
        inA := true
      ia := ia + 1

    if inA then
      j := j + 1
      continue

    -- check if y already in out
    let mut inOut2 : Bool := false
    let mut io2 : Nat := 0
    while io2 < out.size ∧ (inOut2 = false)
      -- Invariant: io2 stays within bounds
      invariant "inv_inOut2_bounds" io2 ≤ out.size
      -- Invariant: if still not found, y is not in scanned prefix out[0..io2)
      invariant "inv_inOut2_nohit" (inOut2 = false) → (∀ t : Nat, t < io2 → out[t]! ≠ y)
      -- Invariant: if found, there is a witness in the scanned prefix
      invariant "inv_inOut2_hit_witness" (inOut2 = true) → (∃ t : Nat, t < io2 ∧ out[t]! = y)
      done_with (io2 = out.size ∨ inOut2 = true)
    do
      if out[io2]! = y then
        inOut2 := true
      io2 := io2 + 1

    if inOut2 then
      j := j + 1
      continue

    out := out.push y
    j := j + 1

  -- insertion sort via swaps
  let mut n : Nat := out.size
  if n <= 1 then
    return out
  else
    let mut idx : Nat := 1
    while idx < n
      -- Invariant: idx stays within bounds
      invariant "inv_sort_idx_bounds" idx ≤ n
      -- Invariant: n tracks current array size
      invariant "inv_sort_n_size" n = out.size
      -- Invariant: out remains duplicate-free through swaps (swaps preserve nodup)
      invariant "inv_sort_nodup" arrayNodup out
      -- Invariant: already-inserted prefix [0,idx) is sorted
      invariant "inv_sort_prefix_sorted" ∀ p q : Nat, p < q → q < idx → out[p]! ≤ out[q]!
    do
      let mut k : Nat := idx
      while 0 < k
        -- Invariant: k is within [0, idx]
        invariant "inv_sort_k_bounds" k ≤ idx
        -- Invariant: n and size remain stable through swaps
        invariant "inv_sort_k_size" n = out.size
        -- Invariant: out stays duplicate-free
        invariant "inv_sort_k_nodup" arrayNodup out
        -- Invariant: elements strictly left of k are sorted
        invariant "inv_sort_k_left_sorted" ∀ p q : Nat, p < q → q < k → out[p]! ≤ out[q]!
        done_with (k = 0 ∨ out[k-1]! ≤ out[k]!)
      do
        if out[k-1]! ≤ out[k]! then
          break
        else
          out := elemSwap! out (k - 1) k
          k := k - 1
      idx := idx + 1

  return out
end Impl

section TestCases
-- Test case 1: example from prompt
-- a = #[1,2,3,4], b = #[3,4,5,6] => symmetric difference = {1,2,5,6}, sorted

def test1_a : Array Int := #[1, 2, 3, 4]
def test1_b : Array Int := #[3, 4, 5, 6]
def test1_Expected : Array Int := #[1, 2, 5, 6]

-- Test case 2: duplicates in input should not duplicate output

def test2_a : Array Int := #[1, 1, 2]
def test2_b : Array Int := #[2, 3]
def test2_Expected : Array Int := #[1, 3]

-- Test case 3: left empty

def test3_a : Array Int := #[]
def test3_b : Array Int := #[4, 5]
def test3_Expected : Array Int := #[4, 5]

-- Test case 4: right empty

def test4_a : Array Int := #[7, 8]
def test4_b : Array Int := #[]
def test4_Expected : Array Int := #[7, 8]

-- Test case 5: identical arrays -> empty symmetric difference

def test5_a : Array Int := #[1, 2, 3]
def test5_b : Array Int := #[1, 2, 3]
def test5_Expected : Array Int := #[]

-- Test case 6: disjoint arrays -> union, sorted

def test6_a : Array Int := #[1, 2, 3]
def test6_b : Array Int := #[4, 5, 6]
def test6_Expected : Array Int := #[1, 2, 3, 4, 5, 6]

-- Test case 7: includes negative numbers and cancellation of common element

def test7_a : Array Int := #[-1, 0, 1]
def test7_b : Array Int := #[0]
def test7_Expected : Array Int := #[-1, 1]

-- Test case 8: unsorted inputs; output still must be sorted and deduped

def test8_a : Array Int := #[3, 1, 2]
def test8_b : Array Int := #[2, 4, 3]
def test8_Expected : Array Int := #[1, 4]

-- Test case 9: many duplicates and overlap

def test9_a : Array Int := #[5, 5, 5]
def test9_b : Array Int := #[5, 6, 6]
def test9_Expected : Array Int := #[6]

-- Recommend to validate: 1, 2, 7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((dissimilarElements test1_a test1_b).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((dissimilarElements test2_a test2_b).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((dissimilarElements test3_a test3_b).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((dissimilarElements test4_a test4_b).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((dissimilarElements test5_a test5_b).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((dissimilarElements test6_a test6_b).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((dissimilarElements test7_a test7_b).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((dissimilarElements test8_a test8_b).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((dissimilarElements test9_a test9_b).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 265, Column 0
-- Message: unsolved goals
-- case refine_1
-- a b result : Array ℤ
-- ⊢ Decidable (symmDiffSpec a b result)
-- Line: prove_postcondition_decidable_for dissimilarElements
-- [ERROR] Line 267, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for dissimilarElements
-- prove_precondition_decidable_for dissimilarElements
-- prove_postcondition_decidable_for dissimilarElements
-- derive_tester_for dissimilarElements
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
--     let arg_1 ← Plausible.SampleableExt.interpSample (Array Int)
--     let res := dissimilarElementsTester arg_0 arg_1
--     pure ((arg_0, arg_1), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct dissimilarElements by
  -- loom_solve <;> (try simp at *; expose_names)
end Proof
