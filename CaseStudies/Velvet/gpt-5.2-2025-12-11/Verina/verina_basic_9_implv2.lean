import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import Init.Data.Array.Lemmas

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    hasCommonElement: Check whether two arrays of integers share at least one element.
    Natural language breakdown:
    1. Inputs are two arrays of integers a and b.
    2. The result is true exactly when there exists an integer x that appears in a and also appears in b.
    3. The result is false exactly when no integer appears in both arrays.
    4. Arrays are always non-null in Lean.
    5. Rejected inputs: both arrays empty; thus we require at least one of the arrays is nonempty.
-/

section Specs
-- There exists an integer value that occurs in both arrays.
-- Note: we deliberately keep this as a Prop and relate the Bool result to it using ↔,
-- to avoid needing a global `Decidable (∃ x, x ∈ a ∧ x ∈ b)` instance.
def HasCommonElem (a : Array Int) (b : Array Int) : Prop :=
  ∃ x : Int, x ∈ a ∧ x ∈ b

-- Precondition: disallow the rejected case where both arrays are empty.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size ≠ 0 ∨ b.size ≠ 0

-- Postcondition: result is true iff there exists a common element.
-- This characterizes the output uniquely.
def postcondition (a : Array Int) (b : Array Int) (result : Bool) : Prop :=
  (result = true ↔ HasCommonElem a b)
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
    -- i never exceeds a.size (init i=0; body increments i by 1 under guard i<a.size)
    invariant 0 ≤ i ∧ i ≤ a.size
    -- If we have not found a match yet, then every scanned a[p] (p<i) differs from every b[q]
    -- (init vacuous at i=0; preserved since inner loop establishes a[i] differs from all b when found stays false)
    invariant found = false → ∀ p : Nat, p < i → ∀ q : Nat, q < b.size → a[p]! ≠ b[q]!
    -- If found is true, we already have a concrete witness indices in bounds with equal values
    -- (init false; preservation: set found only when ai=b[j])
    invariant found = true → ∃ p q : Nat, p < a.size ∧ q < b.size ∧ a[p]! = b[q]!
  do
    let ai := a[i]!
    let mut j : Nat := 0
    while j < b.size ∧ found = false
      -- j never exceeds b.size (init j=0; body increments j by 1 under guard j<b.size)
      invariant 0 ≤ j ∧ j ≤ b.size
      -- If still not found, then ai differs from all already-scanned b[q] (q<j)
      -- (init vacuous at j=0; preserved when ai≠b[j] and we increment j)
      invariant found = false → ∀ q : Nat, q < j → ai ≠ b[q]!
      -- If found becomes true in this inner loop, then there exists a scanned index q<j with ai=b[q]
      -- (preserved since found can only be set at current j, then after increment we have q=j<j+1)
      invariant found = true → ∃ q : Nat, q < j ∧ ai = b[q]!
    do
      if ai = b[j]! then
        found := true
      else
        pure ()
      j := j + 1
    i := i + 1
  return found
end Impl

section TestCases
-- Test case 1: disjoint arrays (given example)
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[4, 5, 6]
def test1_Expected : Bool := false

-- Test case 2: one common element (given example)
def test2_a : Array Int := #[1, 2, 3]
def test2_b : Array Int := #[3, 4, 5]
def test2_Expected : Bool := true

-- Test case 3: common element at different positions (given example)
def test3_a : Array Int := #[7, 8, 9]
def test3_b : Array Int := #[10, 11, 7]
def test3_Expected : Bool := true

-- Test case 4: longer disjoint arrays (given example)
def test4_a : Array Int := #[1, 2, 3, 4]
def test4_b : Array Int := #[5, 6, 7, 8]
def test4_Expected : Bool := false

-- Test case 5: common element at the end of a / start of b (given example)
def test5_a : Array Int := #[1, 2, 3, 4]
def test5_b : Array Int := #[4, 5, 6]
def test5_Expected : Bool := true

-- Test case 6: duplicates present (given example)
def test6_a : Array Int := #[1, 1, 1]
def test6_b : Array Int := #[1, 2, 1]
def test6_Expected : Bool := true

-- Test case 7: singleton arrays with same element (given example)
def test7_a : Array Int := #[0]
def test7_b : Array Int := #[0]
def test7_Expected : Bool := true

-- Test case 8: singleton vs array without that element (given example)
def test8_a : Array Int := #[0]
def test8_b : Array Int := #[-1, 1]
def test8_Expected : Bool := false

-- Test case 9: allowed edge case: a empty, b nonempty
-- There cannot be a common element if one array is empty.
def test9_a : Array Int := #[]
def test9_b : Array Int := #[42]
def test9_Expected : Bool := false

-- Recommend to validate: test1, test2, test7
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
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct hasCommonElement by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0 (a b : Array ℤ)
  (require_1 : precondition a b)
  (found : Bool)
  (i : ℕ)
  (a_2 : i ≤ a.size)
  (invariant_2 : found = false → ∀ p < i, ∀ q < b.size, ¬a[p]! = b[q]!)
  (invariant_3 : found = true → ∃ p < a.size, ∃ x < b.size, a[p]! = b[x]!)
  (i_1 : Bool)
  (i_2 : ℕ)
  (a_1 : True)
  (done_1 : i < a.size → found = true)
  (i_3 : found = i_1 ∧ i = i_2) : postcondition a b i_1 := by
    unfold postcondition
    unfold HasCommonElem 
    apply Iff.intro
    · intro hi
      have: found = true := by grind
      have := invariant_3 this
      cases this with 
      | intro p hp =>
          use a[p]!
          grind
    · intro hx
      have : found = i_1 := by grind
      simp_all
      cases hx with
      | intro w hw =>
          cases hw
          expose_names
          apply done_1
          sorry
          




    

prove_correct hasCommonElement by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
end Proof
