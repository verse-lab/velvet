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
    arraySum: calculate the sum of all the elements in an array of integers.
    Natural language breakdown:
    1. Input is an Array Int named a.
    2. The method conceptually processes the entire array.
    3. The output is an Int equal to the total sum of all elements of a.
    4. The benchmark indicates empty arrays are rejected; therefore, we require a to be non-empty.
    5. For non-empty arrays, the sum is the standard additive sum of all elements.
-/

section Specs
-- Helper Functions
-- We use the standard `Array.sum` for an additive type with a zero.

-- Preconditions
-- Match REJECT_INPUTS: the empty array #[] is rejected.
-- Arrays are never null in Lean, so only non-emptiness is required.

def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postconditions
-- The result is uniquely determined as the array sum.

def postcondition (a : Array Int) (result : Int) : Prop :=
  result = a.sum
end Specs

section Impl
method arraySum (a : Array Int) return (result : Int)
  require precondition a
  ensures postcondition a result
  do
    let mut i := 0
    let mut s : Int := 0
    while i < a.size
      -- Invariant: index stays within bounds for safe access and termination reasoning.
      -- Init: i = 0 so 0 ≤ i ≤ a.size. Preserved: i increments by 1 while i < a.size.
      invariant "inv_bounds" (0 ≤ i ∧ i ≤ a.size)
      -- Invariant: accumulator equals the sum of the prefix processed so far.
      -- Init: i=0, s=0 and (a.extract 0 0).sum = 0.
      -- Preserved: extending the prefix by element i adds a[i]! to both sides.
      invariant "inv_prefix_sum" (s = (a.extract 0 i).sum)
      done_with (i >= a.size)
    do
      s := s + a[i]!
      i := i + 1
    return s
end Impl

section TestCases
-- Test case 1: example from prompt
-- a = #[1,2,3,4,5] => 15

def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Int := 15

-- Test case 2: example from prompt

def test2_a : Array Int := #[13, 14, 15, 16, 17]
def test2_Expected : Int := 75

-- Test case 3: example from prompt (all negative)

def test3_a : Array Int := #[-1, -2, -3]
def test3_Expected : Int := -6

-- Test case 4: example from prompt (cancelling)

def test4_a : Array Int := #[10, -10]
def test4_Expected : Int := 0

-- Test case 5: single element

def test5_a : Array Int := #[42]
def test5_Expected : Int := 42

-- Test case 6: contains zeros

def test6_a : Array Int := #[0, 0, 7, 0]
def test6_Expected : Int := 7

-- Test case 7: mixed positives and negatives

def test7_a : Array Int := #[3, -1, 4, -5, 9]
def test7_Expected : Int := 10

-- Test case 8: larger magnitude Ints

def test8_a : Array Int := #[1000000, -999999, 2]
def test8_Expected : Int := 3

-- Test case 9: non-empty edge case (minimal size = 1, negative)

def test9_a : Array Int := #[-7]
def test9_Expected : Int := -7

-- Recommend to validate: 1, 3, 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((arraySum test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((arraySum test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((arraySum test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((arraySum test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((arraySum test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((arraySum test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((arraySum test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((arraySum test8_a).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((arraySum test9_a).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for arraySum
prove_precondition_decidable_for arraySum
prove_postcondition_decidable_for arraySum
derive_tester_for arraySum
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := arraySumTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct arraySum by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (a : Array ℤ)
    (i : ℕ)
    (s : ℤ)
    (a_2 : i ≤ a.size)
    (if_pos : i < a.size)
    (a_1 : True)
    (h_s_eq_prefix : s = (a.extract 0 i).sum)
    : (a.extract 0 i).push a[i] = a.extract 0 (i + 1) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0_1_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (s : ℤ)
    (a_2 : i ≤ a.size)
    (invariant_inv_prefix_sum : s = (a.extract 0 i).sum)
    (if_pos : i < a.size)
    (a_1 : True)
    (h_s_eq_prefix : s = (a.extract 0 i).sum)
    (h_getBang_eq_getElem : a[i]! = a[i])
    (h_extract_push_getElem : True)
    (h_extract_succ_eq_push_getElem : True)
    (h_extract_push_eq_extract_succ : True)
    (h_sum_congr : True)
    : (a.extract 0 (i + 1)).sum = (a.extract 0 i).sum + a[i] := by
    sorry

theorem goal_0_1
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (s : ℤ)
    (a_2 : i ≤ a.size)
    (invariant_inv_prefix_sum : s = (a.extract 0 i).sum)
    (if_pos : i < a.size)
    (a_1 : True)
    (h_s_eq_prefix : s = (a.extract 0 i).sum)
    (h_getBang_eq_getElem : a[i]! = a[i])
    (h_extract_push_getElem : True)
    (h_extract_succ_eq_push_getElem : True)
    : (a.extract 0 (i + 1)).sum = (a.extract 0 i).sum + a[i] := by
    have h_extract_push_eq_extract_succ : (a.extract 0 i).push a[i] = a.extract 0 (i + 1) := by
      simpa using (goal_0_0 (a := a) (i := i) (s := s) (a_2 := a_2) (if_pos := if_pos) (a_1 := a_1) (h_s_eq_prefix := h_s_eq_prefix))
    have h_sum_congr : ((a.extract 0 i).push a[i]).sum = (a.extract 0 (i + 1)).sum := by
      simpa using congrArg Array.sum h_extract_push_eq_extract_succ
    have h_sum_push : ((a.extract 0 i).push a[i]).sum = (a.extract 0 i).sum + a[i] := by
      (try simp at *; expose_names); exact (goal_0_1_0 a require_1 i s a_2 invariant_inv_prefix_sum if_pos a_1 h_s_eq_prefix h_getBang_eq_getElem h_extract_push_getElem h_extract_succ_eq_push_getElem h_extract_push_eq_extract_succ h_sum_congr); done
    calc
      (a.extract 0 (i + 1)).sum
          = ((a.extract 0 i).push a[i]).sum := by simpa [h_sum_congr] using (Eq.symm h_sum_congr)
      _   = (a.extract 0 i).sum + a[i] := by simpa using h_sum_push

theorem goal_0_2
    (a : Array ℤ)
    (i : ℕ)
    (s : ℤ)
    (if_pos : i < a.size)
    (a_1 : True)
    (h_s_eq_prefix : s = (a.extract 0 i).sum)
    (h_getBang_eq_getElem : a[i]! = a[i])
    (h_sum_extract_succ_getElem : (a.extract 0 (i + 1)).sum = (a.extract 0 i).sum + a[i])
    (h_extract_push_getElem : True)
    (h_extract_succ_eq_push_getElem : True)
    (h_sum_push_getElem : (a.extract 0 (i + 1)).sum = (a.extract 0 i).sum + a[i])
    : (a.extract 0 (i + 1)).sum = (a.extract 0 i).sum + a[i]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (s : ℤ)
    (a_2 : i ≤ a.size)
    (invariant_inv_prefix_sum : s = (a.extract 0 i).sum)
    (if_pos : i < a.size)
    (a_1 : True)
    : s + a[i]! = (a.extract 0 (i + 1)).sum := by
  have h_s_eq_prefix : s = (a.extract 0 i).sum := by (try simp at *; expose_names); exact (invariant_inv_prefix_sum); done
  have h_extract_push_getElem : (a.extract 0 i).push a[i] = a.extract 0 (i + 1) := by (try simp at *; expose_names); exact (goal_0_0 a i s a_2 if_pos a_1 h_s_eq_prefix); done
  have h_extract_succ_eq_push_getElem : a.extract 0 (i + 1) = (a.extract 0 i).push a[i] := by (try simp at *; expose_names); exact (id (Eq.symm h_extract_push_getElem)); done
  have h_getBang_eq_getElem : a[i]! = a[i] := by (try simp at *; expose_names); exact (getElem!_pos a i if_pos); done
  have h_sum_push_getElem : ((a.extract 0 i).push a[i]).sum = (a.extract 0 i).sum + a[i] := by (try simp at *; expose_names); exact (goal_0_1 a require_1 i s a_2 invariant_inv_prefix_sum if_pos a_1 h_s_eq_prefix h_getBang_eq_getElem h_extract_push_getElem h_extract_succ_eq_push_getElem); done
  have h_sum_extract_succ_getElem : (a.extract 0 (i + 1)).sum = (a.extract 0 i).sum + a[i] := by (try simp at *; expose_names); exact (h_sum_push_getElem); done
  have h_sum_extract_succ_getBang : (a.extract 0 (i + 1)).sum = (a.extract 0 i).sum + a[i]! := by (try simp at *; expose_names); exact (goal_0_2 a i s if_pos a_1 h_s_eq_prefix h_getBang_eq_getElem h_sum_extract_succ_getElem h_extract_push_getElem h_extract_succ_eq_push_getElem h_sum_push_getElem); done
  have h_prefix_extend : (a.extract 0 i).sum + a[i]! = (a.extract 0 (i + 1)).sum := by (try simp at *; expose_names); exact (id (Eq.symm h_sum_extract_succ_getBang)); done
  calc
    s + a[i]! = (a.extract 0 i).sum + a[i]! := by simpa [h_s_eq_prefix]
    _ = (a.extract 0 (i + 1)).sum := by simpa using h_prefix_extend

theorem goal_1
    (a : Array ℤ)
    (i : ℕ)
    (s : ℤ)
    (a_2 : i ≤ a.size)
    (invariant_inv_prefix_sum : s = (a.extract 0 i).sum)
    (i_1 : ℕ)
    (s_1 : ℤ)
    (done_1 : a.size ≤ i)
    (i_2 : i = i_1 ∧ s = s_1)
    : postcondition a s_1 := by
  unfold postcondition
  -- reduce to proving `s = a.sum` using `s = s_1`
  have hs : s = s_1 := i_2.2
  -- show `s_1 = a.sum`
  -- rewrite via the invariant and the fact that `i = a.size`
  have hi : i = a.size := le_antisymm a_2 done_1
  -- turn invariant into a full-sum statement
  have hsum : s = a.sum := by
    -- rewrite the invariant at `i = a.size`
    have : s = (a.extract 0 a.size).sum := by
      simpa [hi] using invariant_inv_prefix_sum
    -- extract of full range is the array itself
    simpa [Array.extract_size] using this
  -- finish by rewriting with `hs`
  -- (we have s = s_1, but need s_1 = a.sum)
  calc
    s_1 = s := by simpa using hs.symm
    _ = a.sum := hsum


prove_correct arraySum by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a require_1 i s a_2 invariant_inv_prefix_sum if_pos a_1)
  exact (goal_1 a i s a_2 invariant_inv_prefix_sum i_1 s_1 done_1 i_2)
end Proof
