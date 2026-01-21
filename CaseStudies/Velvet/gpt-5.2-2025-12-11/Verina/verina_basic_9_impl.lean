import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas

import Init.Data.Array.Lemmas

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    hasCommonElement: Check whether two arrays of integers share any common element.
    Natural language breakdown:
    1. Inputs are two arrays `a` and `b` containing integers.
    2. The result is a boolean.
    3. The result is true exactly when there exists at least one integer value `x`
       that is an element of `a` and also an element of `b`.
    4. The result is false exactly when there is no integer value present in both arrays.
    5. Reject inputs: both arrays empty are considered invalid for this task.
-/

section Specs
-- Preconditions are intentionally minimal:
-- the only rejected input mentioned is the case where both arrays are empty.

def precondition (a : Array Int) (b : Array Int) : Prop :=
  ¬(a.size = 0 ∧ b.size = 0)

-- Make the precondition decidable so tests can use `decide`.
instance (a : Array Int) (b : Array Int) : Decidable (precondition a b) := by
  dsimp [precondition]
  infer_instance

-- Postcondition: the boolean result matches existence of a common element.
-- We keep `result = true ↔ ...` to avoid relying on any coercion from Bool to Prop.

def postcondition (a : Array Int) (b : Array Int) (result : Bool) : Prop :=
  (result = true ↔ (∃ x : Int, x ∈ a ∧ x ∈ b))
end Specs

section Impl
method hasCommonElement (a : Array Int) (b : Array Int)
  return (result : Bool)
  require precondition a b
  ensures postcondition a b result
  do
    let mut found := false
    let mut i : Nat := 0
    while i < a.size ∧ found = false
      -- Invariant: `i` stays within bounds of `a` (supports safe access when combined with the loop guard).
      -- init: i=0; step: i:=i+1 preserves i ≤ a.size; exit: i=a.size.
      invariant "inv_outer_bounds" i ≤ a.size
      -- Invariant: If `found` is still false, then no common element exists among the already-checked prefix a[0..i).
      -- init: vacuous at i=0; preserved: inner loop establishes a[i] differs from all of b, then i increments.
      invariant "inv_outer_noCommon_prefix" (found = false → ∀ p : Nat, p < i → ∀ q : Nat, q < b.size → a[p]! ≠ b[q]!)
      -- Invariant: If `found` is true, we have witnessed a common element via some indices in bounds.
      -- preserved because `found` only ever flips to true when an equality is observed.
      invariant "inv_outer_found_witness" (found = true → ∃ p : Nat, p < a.size ∧ ∃ q : Nat, q < b.size ∧ a[p]! = b[q]!)
    do
      let mut j : Nat := 0
      while j < b.size ∧ found = false
        -- Invariant: `j` stays within bounds of `b` (supports safe access when combined with the loop guard).
        -- init: j=0; step: j:=j+1 preserves j ≤ b.size; exit: j=b.size.
        invariant "inv_inner_bounds" j ≤ b.size
        -- Invariant: While the inner loop runs, the outer index is in bounds (from the outer loop guard i < a.size).
        -- This ensures all occurrences of `a[i]!` are safe.
        invariant "inv_inner_i_inBounds" i < a.size
        -- Invariant: If still not found, then current a[i] differs from all already-checked b[0..j).
        -- init: vacuous at j=0; preserved by checking b[j] then incrementing j.
        invariant "inv_inner_scanned" (found = false → ∀ q : Nat, q < j → a[i]! ≠ b[q]!)
        -- Invariant: If found becomes true, we can witness a common element via some indices in bounds.
        invariant "inv_inner_found_witness" (found = true → ∃ p : Nat, p < a.size ∧ ∃ q : Nat, q < b.size ∧ a[p]! = b[q]!)
      do
        if a[i]! = b[j]! then
          found := true
        j := j + 1
      i := i + 1
    return found
end Impl

section TestCases
-- Test case 1: disjoint arrays (example from prompt)
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[4, 5, 6]
def test1_Expected : Bool := false

-- Test case 2: common element 3 (example from prompt)
def test2_a : Array Int := #[1, 2, 3]
def test2_b : Array Int := #[3, 4, 5]
def test2_Expected : Bool := true

-- Test case 3: common element 7 (example from prompt)
def test3_a : Array Int := #[7, 8, 9]
def test3_b : Array Int := #[10, 11, 7]
def test3_Expected : Bool := true

-- Test case 4: larger disjoint arrays (example from prompt)
def test4_a : Array Int := #[1, 2, 3, 4]
def test4_b : Array Int := #[5, 6, 7, 8]
def test4_Expected : Bool := false

-- Test case 5: common element 4 (example from prompt)
def test5_a : Array Int := #[1, 2, 3, 4]
def test5_b : Array Int := #[4, 5, 6]
def test5_Expected : Bool := true

-- Test case 6: duplicates in arrays still count as common (example from prompt)
def test6_a : Array Int := #[1, 1, 1]
def test6_b : Array Int := #[1, 2, 1]
def test6_Expected : Bool := true

-- Test case 7: singleton arrays with same element (example from prompt)
def test7_a : Array Int := #[0]
def test7_b : Array Int := #[0]
def test7_Expected : Bool := true

-- Test case 8: singleton vs two elements, no common (example from prompt)
def test8_a : Array Int := #[0]
def test8_b : Array Int := #[-1, 1]
def test8_Expected : Bool := false

-- Test case 9: reject-input example (both empty) as a precondition check
-- Here we test the precondition computation rather than a function output.
def test9_a : Array Int := #[]
def test9_b : Array Int := #[]
def test9_PreconditionHolds : Bool := decide (precondition test9_a test9_b)
def test9_Expected : Bool := false

-- Recommend to validate: 1, 2, 7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((hasCommonElement test1_a test1_b).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((hasCommonElement test2_a test2_b).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((hasCommonElement test3_a test3_b).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((hasCommonElement test4_a test4_b).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((hasCommonElement test5_a test5_b).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((hasCommonElement test6_a test6_b).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((hasCommonElement test7_a test7_b).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((hasCommonElement test8_a test8_b).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((hasCommonElement test9_a test9_b).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for hasCommonElement
prove_precondition_decidable_for hasCommonElement
prove_postcondition_decidable_for hasCommonElement
derive_tester_for hasCommonElement
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := hasCommonElementTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct hasCommonElement by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0 (a : Array ℤ)
    (b : Array ℤ)
    (require_1 : precondition a b)
    (found : Bool)
    (i : ℕ)
    (invariant_inv_outer_bounds : i ≤ a.size)
    (invariant_inv_outer_noCommon_prefix : found = false → ∀ p < i, ∀ q < b.size, ¬a[p]! = b[q]!)
    (invariant_inv_outer_found_witness : found = true → ∃ p < a.size, ∃ q < b.size, a[p]! = b[q]!)
    (i_1 : Bool)
    (i_2 : ℕ)
    (done_1 : i < a.size → found = true)
    (i_3 : found = i_1 ∧ i = i_2) : postcondition a b i_1 := by
  classical
  rcases i_3 with ⟨hfound, hi⟩
  unfold postcondition
  constructor
  · intro hi1true
    have hfoundTrue : found = true := by simpa [hfound] using hi1true
    rcases invariant_inv_outer_found_witness hfoundTrue with ⟨p, hp, q, hq, hpq⟩
    refine ⟨a[p]!, ?_, ?_⟩
    · -- a[p]! ∈ a
      have hm : a[p]! ∈ a := by
        refine (Array.mem_iff_getElem).2 ?_
        refine ⟨p, hp, ?_⟩
        -- relate getElem and get! on an in-bounds index
        simpa [Array.get!, hp]
      simpa using hm
    · -- a[p]! ∈ b
      have hm : b[q]! ∈ b := by
        refine (Array.mem_iff_getElem).2 ?_
        refine ⟨q, hq, ?_⟩
        simpa [Array.get!, hq]
      simpa [hpq] using hm
  · intro hex
    -- prove i_1 = true by contradiction: if i_1 = false then no common element exists
    by_contra hi1ne
    have hi1false : i_1 = false := by
      cases h : i_1 <;> simp [h] at hi1ne ⊢
    have hfoundFalse : found = false := by simpa [hfound, hi1false]
    have hnotlt : ¬ i < a.size := by
      intro hlt
      have : found = true := done_1 hlt
      simpa [hfoundFalse] using this
    have hge : a.size ≤ i := Nat.le_of_not_gt hnotlt
    have hEq : i = a.size := Nat.le_antisymm invariant_inv_outer_bounds hge

    -- show existence of common element contradicts "noCommon_prefix" at i = a.size
    rcases hex with ⟨x, hxa, hxb⟩
    rcases (Array.mem_iff_getElem).1 hxa with ⟨p, hp, hpx⟩
    rcases (Array.mem_iff_getElem).1 hxb with ⟨q, hq, hqx⟩

    have hap : a[p]! = x := by
      -- hpx : a[p]'hp = x
      simpa [Array.get!, hp] using hpx
    have hbq : b[q]! = x := by
      simpa [Array.get!, hq] using hqx

    have hEqpq : a[p]! = b[q]! := by
      calc
        a[p]! = x := hap
        _ = b[q]! := by symm; exact hbq

    have hp' : p < i := by simpa [hEq] using hp
    have hnoc : ¬ a[p]! = b[q]! :=
      invariant_inv_outer_noCommon_prefix hfoundFalse p hp' q hq
    exact hnoc hEqpq


prove_correct hasCommonElement by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
end Proof
