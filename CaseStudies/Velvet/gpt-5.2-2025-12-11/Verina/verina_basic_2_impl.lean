import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import Batteries.Data.Array.Basic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findSmallest: Find the smallest number in an array of natural numbers
    Natural language breakdown:
    1. Given an array of natural numbers, find the smallest element
    2. If the array is empty, return none
    3. If the array is non-empty, return some(min) where min is the smallest element
    4. The smallest element must be in the array
    5. The smallest element must be less than or equal to all other elements
    6. For non-empty arrays, the result uniquely identifies the minimum value
    7. This is a property-based specification: we specify what the minimum must satisfy
       (membership and minimality), not how to compute it
    8. Edge cases:
       - Empty array: return none
       - Single element: return that element
       - All equal elements: return that common value
       - Array with duplicates of minimum: return the minimum value
-/

section Specs

-- Precondition: no requirements on input array
def precondition (s : Array Nat) :=
  True

-- Postcondition: characterize the result based on array emptiness
def postcondition (s : Array Nat) (result : Option Nat) :=
  match result with
  | none => s.size = 0
  | some min =>
      s.size > 0 ∧
      (∃ i, i < s.size ∧ s[i]! = min) ∧
      (∀ j, j < s.size → min ≤ s[j]!)

end Specs

section Impl

method findSmallest (s: Array Nat)
  return (result: Option Nat)
  require precondition s
  ensures postcondition s result
  do
  if s.size = 0 then
    return none
  else
    let mut minIndex := 0
    let mut i := 1
    while i < s.size
      -- Invariant 1: i stays in valid range starting from 1
      -- Initialization: i = 1 at entry, which satisfies 1 ≤ 1 ≤ s.size (since s.size > 0)
      -- Preservation: i increments but stays ≤ s.size due to loop condition
      invariant 1 ≤ i ∧ i ≤ s.size
      -- Invariant 2: minIndex points to a valid index in the scanned portion
      -- Initialization: minIndex = 0 < 1 = i holds at entry
      -- Preservation: when updated, minIndex becomes i (before increment), maintaining minIndex < i+1
      invariant 0 ≤ minIndex ∧ minIndex < i
      -- Invariant 3: minIndex is always a valid array index
      -- Follows from invariant 2 and i ≤ s.size
      invariant minIndex < s.size
      -- Invariant 4: s[minIndex] is the minimum of all elements scanned so far [0..i)
      -- Initialization: At i=1, only s[0] scanned, and minIndex=0, so s[minIndex]! ≤ s[0]! trivially holds
      -- Preservation: If s[i]! < s[minIndex]!, we update minIndex to i, maintaining property for [0..i+1)
      --               Otherwise, s[minIndex]! ≤ s[i]! already, so property holds for [0..i+1)
      -- Sufficiency: When i = s.size, this gives us the global minimum and its index
      invariant ∀ j, 0 ≤ j ∧ j < i → s[minIndex]! ≤ s[j]!
      done_with i = s.size
    do
      if s[i]! < s[minIndex]! then
        minIndex := i
      else
        pure ()
      i := i + 1
    return some s[minIndex]!

end Impl

section TestCases

-- Test case 1: Example from problem - array with duplicates
def test1_s : Array Nat := #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
def test1_Expected : Option Nat := some 1

-- Test case 2: Minimum at start (zero)
def test2_s : Array Nat := #[0, 1, 2, 3, 4, 5]
def test2_Expected : Option Nat := some 0

-- Test case 3: Single element array
def test3_s : Array Nat := #[1]
def test3_Expected : Option Nat := some 1

-- Test case 4: All elements the same
def test4_s : Array Nat := #[10, 10, 10]
def test4_Expected : Option Nat := some 10

-- Test case 5: Minimum at end
def test5_s : Array Nat := #[3, 2, 2, 2, 2, 2, 2, 1]
def test5_Expected : Option Nat := some 1

-- Test case 6: Single zero
def test6_s : Array Nat := #[0]
def test6_Expected : Option Nat := some 0

-- Test case 7: Descending order, minimum at end
def test7_s : Array Nat := #[100, 99, 98]
def test7_Expected : Option Nat := some 98

-- Test case 8: Empty array
def test8_s : Array Nat := #[]
def test8_Expected : Option Nat := none

-- Recommend to validate: 1, 7, 8

end TestCases

section Assertions

-- Test case 1

#assert_same_evaluation #[((findSmallest test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((findSmallest test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((findSmallest test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((findSmallest test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((findSmallest test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((findSmallest test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((findSmallest test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((findSmallest test8_s).run), DivM.res test8_Expected ]

end Assertions

section Pbt

-- PBT disabled due to build error:
-- [ERROR] Line 147, Column 0
-- Message: unsolved goals
-- s : Array ℕ
-- result : Option ℕ
-- ⊢ Decidable (postcondition s result)
-- Line: prove_postcondition_decidable_for findSmallest
-- [ERROR] Line 149, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do


-- extract_program_for findSmallest
-- prove_precondition_decidable_for findSmallest
-- prove_postcondition_decidable_for findSmallest
-- derive_tester_for findSmallest
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Array Nat)
--     let res := findSmallestTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    

end Pbt

section Proof

-- prove_correct findSmallest by
--   loom_solve <;> (try simp at *; expose_names)


theorem goal_0 (s : Array ℕ)
    (require_1 : precondition s)
    (if_pos : s = #[]) : postcondition s none := by
  unfold postcondition
  rw [if_pos]
  rfl


theorem goal_1 (s : Array ℕ)
    (require_1 : precondition s)
    (i : ℕ)
    (minIndex : ℕ)
    (a : 1 ≤ i)
    (a_1 : i ≤ s.size)
    (a_3 : minIndex < i)
    (invariant_3 : minIndex < s.size)
    (done_1 : i = s.size)
    (i_1 : ℕ)
    (minIndex_1 : ℕ)
    (if_neg : ¬s = #[])
    (a_2 : True)
    (invariant_4 : ∀ j < i, s[minIndex]! ≤ s[j]!)
    (i_2 : i = i_1 ∧ minIndex = minIndex_1) : postcondition s (some s[minIndex_1]!) := by
  unfold postcondition
  constructor
  · -- Prove s.size > 0
    omega
  constructor
  · -- Prove ∃ i, i < s.size ∧ s[i]! = s[minIndex_1]!
    use minIndex_1
    constructor
    · have : minIndex = minIndex_1 := i_2.2
      rw [← this]
      exact invariant_3
    · rfl
  · -- Prove ∀ j, j < s.size → s[minIndex_1]! ≤ s[j]!
    intro j hj
    have h_minIndex : minIndex = minIndex_1 := i_2.2
    have h_i : i = s.size := done_1
    rw [← h_minIndex]
    have : j < i := by rw [h_i]; exact hj
    exact invariant_4 j this



prove_correct findSmallest by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s require_1 if_pos)
  exact (goal_1 s require_1 i minIndex a a_1 a_3 invariant_3 done_1 i_1 minIndex_1 if_neg a_2 invariant_4 i_2)

end Proof
