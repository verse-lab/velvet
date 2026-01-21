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
    differenceMinMax: compute the difference between the maximum and minimum values of a nonempty array of Int.
    Natural language breakdown:
    1. The input is an array `a : Array Int`.
    2. The input array is assumed to be non-empty.
    3. Let `mn` be the minimum value occurring in `a` and `mx` be the maximum value occurring in `a`.
    4. The returned integer is `mx - mn`.
    5. The result must be 0 when all elements are equal or when the array has exactly one element.
    6. The specification should describe `mn` and `mx` as bounds achieved by some array elements.
-/

section Specs
-- Helper predicate: value occurs in array
def InArray (a : Array Int) (v : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = v

-- Helper predicate: `mn` is a minimum value achieved in the array
def IsMinOfArray (a : Array Int) (mn : Int) : Prop :=
  InArray a mn ∧ (∀ (i : Nat), i < a.size → mn ≤ a[i]!)

-- Helper predicate: `mx` is a maximum value achieved in the array
def IsMaxOfArray (a : Array Int) (mx : Int) : Prop :=
  InArray a mx ∧ (∀ (i : Nat), i < a.size → a[i]! ≤ mx)

-- Precondition: array is nonempty
-- We use `a.size ≠ 0` which is equivalent to `a ≠ #[]` via `Array.size_eq_zero_iff`.
def precondition (a : Array Int) : Prop :=
  a.size ≠ 0

-- Postcondition: result equals (max - min) for some achieved max/min bounds.
-- We avoid specifying an algorithm; instead we characterize the unique value via existence of
-- extremal witnesses and defining equation.
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (mn : Int) (mx : Int),
    IsMinOfArray a mn ∧
    IsMaxOfArray a mx ∧
    result = mx - mn
end Specs

section Impl
method differenceMinMax (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
    let mut mn := a[0]!
    let mut mx := a[0]!

    let mut i : Nat := 1
    while i < a.size
      -- Invariant: index stays within bounds (initially i=1; preserved by i := i+1; needed to justify accesses and to cover all elements on exit)
      invariant "diffMinMax_i_bounds" 1 ≤ i ∧ i ≤ a.size
      -- Invariant: mn is a minimum among the elements seen so far (0..i-1), and is achieved in that prefix
      -- Initialization: mn=a[0]! witnessed by j=0; Preservation: updating mn to v maintains min property; Sufficient with i=a.size to get global min.
      invariant "diffMinMax_mn_prefix_min" (∃ j : Nat, j < i ∧ a[j]! = mn) ∧ (∀ j : Nat, j < i → mn ≤ a[j]!)
      -- Invariant: mx is a maximum among the elements seen so far (0..i-1), and is achieved in that prefix
      -- Initialization: mx=a[0]! witnessed by j=0; Preservation: updating mx to v maintains max property; Sufficient with i=a.size to get global max.
      invariant "diffMinMax_mx_prefix_max" (∃ j : Nat, j < i ∧ a[j]! = mx) ∧ (∀ j : Nat, j < i → a[j]! ≤ mx)
    do
      let v := a[i]!
      if v < mn then
        mn := v
      else
        pure ()
      if v > mx then
        mx := v
      else
        pure ()
      i := i + 1

    return (mx - mn)
end Impl

section TestCases
-- Test case 1: example from prompt
-- max = 9, min = 1, difference = 8
def test1_a : Array Int := #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
def test1_Expected : Int := 8

-- Test case 2: increasing positives
def test2_a : Array Int := #[10, 20, 30, 40, 50]
def test2_Expected : Int := 40

-- Test case 3: decreasing negatives
def test3_a : Array Int := #[-10, -20, -30, -40, -50]
def test3_Expected : Int := 40

-- Test case 4: singleton array
def test4_a : Array Int := #[7]
def test4_Expected : Int := 0

-- Test case 5: all equal
def test5_a : Array Int := #[5, 5, 5, 5]
def test5_Expected : Int := 0

-- Test case 6: mixed signs
def test6_a : Array Int := #[1, -1, 2, -2]
def test6_Expected : Int := 4

-- Test case 7: two elements, already ordered
def test7_a : Array Int := #[2, 10]
def test7_Expected : Int := 8

-- Test case 8: two elements, reversed order
def test8_a : Array Int := #[10, 2]
def test8_Expected : Int := 8

-- Test case 9: includes Int.min/Int.max like extremes (small manageable)
-- Here: max = 0, min = -2147483648, difference = 2147483648
def test9_a : Array Int := #[-2147483648, 0, -1]
def test9_Expected : Int := 2147483648

-- Reject input (documented): empty array should violate precondition
def reject1_a : Array Int := #[]

-- Recommend to validate: 1, 4, 6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((differenceMinMax test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((differenceMinMax test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((differenceMinMax test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((differenceMinMax test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((differenceMinMax test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((differenceMinMax test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((differenceMinMax test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((differenceMinMax test8_a).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((differenceMinMax test9_a).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 164, Column 0
-- Message: unsolved goals
-- a : Array ℤ
-- result : ℤ
-- ⊢ Decidable (postcondition a result)
-- Line: prove_postcondition_decidable_for differenceMinMax
-- [ERROR] Line 166, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for differenceMinMax
-- prove_precondition_decidable_for differenceMinMax
-- prove_postcondition_decidable_for differenceMinMax
-- derive_tester_for differenceMinMax
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
--     let res := differenceMinMaxTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct differenceMinMax by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (a : Array ℤ)
    (require_1 : precondition a)
    : 1 ≤ a.size := by
    intros; expose_names; exact (Nat.one_le_iff_ne_zero.mpr require_1); done

theorem goal_1
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (mn : ℤ)
    (mx : ℤ)
    (a_1 : 1 ≤ i)
    (a_2 : i ≤ a.size)
    (a_3 : ∃ j < i, a[j]! = mn)
    (a_4 : ∀ j < i, mn ≤ a[j]!)
    (a_5 : ∃ j < i, a[j]! = mx)
    (a_6 : ∀ j < i, a[j]! ≤ mx)
    (i_1 : ℕ)
    (i_2 : ℤ)
    (mx_1 : ℤ)
    (done_1 : a.size ≤ i)
    (i_3 : i = i_1 ∧ mn = i_2 ∧ mx = mx_1)
    : postcondition a (mx_1 - i_2) := by
  rcases i_3 with ⟨hi, hmn, hmx⟩
  have hiSize : i = a.size := Nat.le_antisymm a_2 done_1

  refine ⟨i_2, mx_1, ?_, ?_, rfl⟩
  · -- IsMinOfArray a i_2
    constructor
    · -- InArray a i_2
      rcases a_3 with ⟨j, hjlt, hjEq⟩
      refine ⟨j, ?_, ?_⟩
      · simpa [hiSize] using hjlt
      · simpa [hmn] using hjEq
    · -- ∀ k < a.size, i_2 ≤ a[k]!
      intro k hk
      have : mn ≤ a[k]! := a_4 k (by simpa [hiSize] using hk)
      simpa [hmn] using this
  · -- IsMaxOfArray a mx_1
    constructor
    · -- InArray a mx_1
      rcases a_5 with ⟨j, hjlt, hjEq⟩
      refine ⟨j, ?_, ?_⟩
      · simpa [hiSize] using hjlt
      · simpa [hmx] using hjEq
    · -- ∀ k < a.size, a[k]! ≤ mx_1
      intro k hk
      have : a[k]! ≤ mx := a_6 k (by simpa [hiSize] using hk)
      simpa [hmx] using this


prove_correct differenceMinMax by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a require_1)
  exact (goal_1 a require_1 i mn mx a_1 a_2 a_3 a_4 a_5 a_6 i_1 i_2 mx_1 done_1 i_3)
end Proof
