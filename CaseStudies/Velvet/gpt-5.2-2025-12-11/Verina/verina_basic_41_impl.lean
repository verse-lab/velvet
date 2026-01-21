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
    hasOnlyOneDistinctElement: determine whether an array of integers contains only one distinct element.
    Natural language breakdown:
    1. Input is an array `a : Array Int`.
    2. The output is a Boolean.
    3. The result is true if the array is empty.
    4. The result is true if the array is nonempty and every element equals the first element.
    5. The result is false if there exist two indices in range whose elements are different.
    6. Arrays are assumed non-null (always true in Lean); no additional input validity is required.
-/

section Specs
-- `atMostOneDistinct a` means: `a` has at most one distinct value.
-- This is characterized observationally:
-- - if the array is empty, the property holds;
-- - otherwise every element equals the first element.
-- (This matches “only one distinct element” while also treating empty as true.)
def atMostOneDistinct (a : Array Int) : Prop :=
  a.size = 0 ∨ (∀ (i : Nat), i < a.size → a[i]! = a[0]!)

-- No preconditions: empty arrays are allowed by the problem statement.
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is true iff the array is empty or all elements equal the first element.
def postcondition (a : Array Int) (result : Bool) : Prop :=
  result ↔ atMostOneDistinct a
end Specs

section Impl
method hasOnlyOneDistinctElement (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
  if a.size = 0 then
    return true
  else
    let base := a[0]!
    let mut i : Nat := 0
    let mut ok : Bool := true
    while (i < a.size ∧ ok)
      -- i always stays within array bounds; needed for safe indexing and to relate prefix to whole array.
      invariant "inv_bounds" i ≤ a.size
      -- If ok is true, all elements in the already-checked prefix [0,i) equal base.
      -- Init: i=0 holds trivially. Pres: when ok stays true, we just checked a[i]=base then increment.
      invariant "inv_prefix_all_eq_if_ok" (ok = true → (∀ j : Nat, j < i → a[j]! = base))
      -- If ok is false, we have already found a counterexample in the checked prefix.
      -- Pres: once set to false, it stays false and i only increases.
      invariant "inv_witness_if_not_ok" (ok = false → (∃ j : Nat, j < i ∧ a[j]! ≠ base))
      done_with (i >= a.size ∨ ok = false)
    do
      if a[i]! != base then
        ok := false
      i := i + 1
    return ok
end Impl

section TestCases
-- Test case 1: provided example, all equal
-- IMPORTANT: If the problem description contains an example, this must be test case 1.
def test1_a : Array Int := #[1, 1, 1]
def test1_Expected : Bool := true

-- Test case 2: provided example, has at least two distinct elements
def test2_a : Array Int := #[1, 2, 1]
def test2_Expected : Bool := false

-- Test case 3: provided example, many distinct
def test3_a : Array Int := #[3, 4, 5, 6]
def test3_Expected : Bool := false

-- Test case 4: provided example, single element
def test4_a : Array Int := #[7]
def test4_Expected : Bool := true

-- Test case 5: provided example, all zeros
def test5_a : Array Int := #[0, 0, 0, 0]
def test5_Expected : Bool := true

-- Test case 6: provided example, one different among equals
def test6_a : Array Int := #[0, 0, 1, 0]
def test6_Expected : Bool := false

-- Test case 7: empty array (edge case; per description result should be true)
def test7_a : Array Int := #[]
def test7_Expected : Bool := true

-- Test case 8: negative values all equal
def test8_a : Array Int := #[-2, -2, -2]
def test8_Expected : Bool := true

-- Test case 9: two elements different (includes negative)
def test9_a : Array Int := #[5, -5]
def test9_Expected : Bool := false

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test2, test7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((hasOnlyOneDistinctElement test1_a).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((hasOnlyOneDistinctElement test2_a).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((hasOnlyOneDistinctElement test3_a).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((hasOnlyOneDistinctElement test4_a).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((hasOnlyOneDistinctElement test5_a).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((hasOnlyOneDistinctElement test6_a).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((hasOnlyOneDistinctElement test7_a).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((hasOnlyOneDistinctElement test8_a).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((hasOnlyOneDistinctElement test9_a).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for hasOnlyOneDistinctElement
prove_precondition_decidable_for hasOnlyOneDistinctElement
prove_postcondition_decidable_for hasOnlyOneDistinctElement
derive_tester_for hasOnlyOneDistinctElement
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := hasOnlyOneDistinctElementTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct hasOnlyOneDistinctElement by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (a : Array ℤ)
    (require_1 : precondition a)
    (if_pos : a = #[])
    : postcondition a true := by
    -- unfold the spec
    unfold postcondition
    -- reduce `true ↔ P` to `P`
    simp
    -- prove `atMostOneDistinct a` using that `a` is empty
    unfold atMostOneDistinct
    left
    -- rewrite by the fact that `a = #[]` and simplify size
    simpa [if_pos]

theorem goal_1
    (a : Array ℤ)
    (require_1 : precondition a)
    (i : ℕ)
    (ok : Bool)
    (invariant_inv_bounds : i ≤ a.size)
    (invariant_inv_prefix_all_eq_if_ok : ok = true → ∀ j < i, a[j]! = a[0]!)
    (invariant_inv_witness_if_not_ok : ok = false → ∃ j < i, ¬a[j]! = a[0]!)
    (i_1 : ℕ)
    (ok_1 : Bool)
    (if_neg : ¬a = #[])
    (done_1 : a.size ≤ i ∨ ok = false)
    (i_2 : i = i_1 ∧ ok = ok_1)
    : postcondition a ok_1 := by
    unfold postcondition
    rcases i_2 with ⟨hi, hok⟩
    -- rewrite everything to use `ok` (and `i`) directly
    subst hi
    subst hok
    -- goal: ok ↔ atMostOneDistinct a
    unfold atMostOneDistinct
    have hneSize : a.size ≠ 0 := by
      intro hsz
      apply if_neg
      exact (Array.size_eq_zero_iff.mp hsz)
    constructor
    · intro hokTrue
      -- since ok=true, cannot have terminated by ok=false; must have a.size ≤ i
      have hsz_le_i : a.size ≤ i := by
        cases done_1 with
        | inl h => exact h
        | inr hokFalse =>
          exfalso
          exact (by simpa [hokTrue] using hokFalse)
      right
      intro j hjSz
      have hjI : j < i := Nat.lt_of_lt_of_le hjSz hsz_le_i
      exact (invariant_inv_prefix_all_eq_if_ok hokTrue) j hjI
    · intro hatMost
      -- `a.size=0` disjunct impossible since a ≠ #[]
      have hall : ∀ k : Nat, k < a.size → a[k]! = a[0]! := by
        cases hatMost with
        | inl hsz =>
          exfalso
          exact hneSize hsz
        | inr hall => exact hall
      -- show ok=true; otherwise we get a witness contradicting `hall`
      by_contra hokNeTrue
      have hokFalse : ok = false := by
        cases ok <;> simp at hokNeTrue ⊢
      rcases invariant_inv_witness_if_not_ok hokFalse with ⟨j, hjLtI, hne⟩
      have hjLtSz : j < a.size := Nat.lt_of_lt_of_le hjLtI invariant_inv_bounds
      have hEq : a[j]! = a[0]! := hall j hjLtSz
      exact hne hEq


prove_correct hasOnlyOneDistinctElement by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a require_1 if_pos)
  exact (goal_1 a require_1 i ok invariant_inv_bounds invariant_inv_prefix_all_eq_if_ok invariant_inv_witness_if_not_ok i_1 ok_1 if_neg done_1 i_2)
end Proof
