import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    increasingTriplet: Determine if there exists a strictly increasing triplet in an array
    Natural language breakdown:
    1. We have an input list of integers (nums)
    2. We need to find if there exist three indices i, j, k such that i < j < k
    3. At these indices, the values must be strictly increasing: nums[i] < nums[j] < nums[k]
    4. The function returns true if such a triplet exists, false otherwise
    5. Edge cases:
       - Empty list: no triplet possible, return false
       - List with fewer than 3 elements: no triplet possible, return false
       - Strictly decreasing list: no triplet exists, return false
       - Any list with an increasing subsequence of length 3: return true
    6. Property-oriented specification:
       - result = true ↔ there exist indices i < j < k with nums[i] < nums[j] < nums[k]
       - The indices must be valid (all less than list length)
-/

section Specs
-- Helper predicate: there exists a strictly increasing triplet
def hasIncreasingTriplet (nums : List Int) : Prop :=
  ∃ i j k : Nat, i < j ∧ j < k ∧ k < nums.length ∧
    nums[i]! < nums[j]! ∧ nums[j]! < nums[k]!

-- Postcondition: result is true iff such a triplet exists
def ensures1 (nums : List Int) (result : Bool) :=
  result = true ↔ hasIncreasingTriplet nums

def precondition (nums : List Int) :=
  True  -- no preconditions

def postcondition (nums : List Int) (result : Bool) :=
  ensures1 nums result
end Specs

section Impl
method increasingTriplet (nums : List Int)
  return (result : Bool)
  require precondition nums
  ensures postcondition nums result
  do
  -- Handle edge cases: need at least 3 elements
  if nums.length < 3 then
    return false
  else
    -- Track the smallest and second smallest values for potential triplet
    -- first: smallest value seen so far
    -- second: smallest value that could be the middle of a triplet
    let mut first := nums[0]!
    let mut second : Option Int := none
    let mut found := false
    let mut i := 1

    while i < nums.length
      -- Invariant 1: Loop index bounds
      -- Initialization: i starts at 1, nums.length >= 3
      -- Preservation: i increments by 1, loop exits when i >= nums.length
      -- Sufficiency: ensures we've processed all elements when loop terminates
      invariant "i_bounds" 1 ≤ i ∧ i ≤ nums.length

      -- Invariant 2: If found is true, a triplet exists
      -- Initialization: found starts false, trivially satisfied
      -- Preservation: found only set true when curr > s (where second = some s)
      -- Sufficiency: directly establishes postcondition when found = true
      invariant "found_implies_triplet" found = true → hasIncreasingTriplet nums

      -- Invariant 3: If second is some s, there exists earlier values forming potential triplet start
      -- Initialization: second starts as none, trivially satisfied
      -- Preservation: second only updated to some curr when curr > first (first was seen earlier)
      -- Sufficiency: helps establish triplet when third element found
      invariant "second_valid" second.isSome → ∃ j k : Nat, j < k ∧ k < i ∧ nums[j]! < second.get!

      -- Invariant 4: If no triplet found yet in prefix, no triplet exists up to i
      -- This captures the completeness: if we haven't found anything, there's nothing to find
      invariant "completeness" found = false →
        (∀ a b c : Nat, a < b → b < c → c < i → ¬(nums[a]! < nums[b]! ∧ nums[b]! < nums[c]!))

      done_with i = nums.length
    do
      let curr := nums[i]!
      match second with
      | some s =>
        if curr > s then
          -- Found triplet: first < second < curr
          found := true
        else
          if curr <= first then
            first := curr
          else
            -- curr > first but curr <= second, update second
            second := some curr
      | none =>
        if curr > first then
          -- Found potential second element
          second := some curr
        else
          -- Update first to be smaller
          first := curr
      i := i + 1

    return found
end Impl

section TestCases
-- Test case 1: Simple increasing sequence [1, 2, 3] - example from problem
def test1_nums : List Int := [1, 2, 3]
def test1_Expected : Bool := true

-- Test case 2: Strictly decreasing sequence [5, 4, 3, 2, 1]
def test2_nums : List Int := [5, 4, 3, 2, 1]
def test2_Expected : Bool := false

-- Test case 3: Mixed sequence with triplet [2, 1, 5, 0, 4, 6]
def test3_nums : List Int := [2, 1, 5, 0, 4, 6]
def test3_Expected : Bool := true

-- Test case 4: Another mixed sequence with triplet [1, 5, 0, 4, 1, 3]
def test4_nums : List Int := [1, 5, 0, 4, 1, 3]
def test4_Expected : Bool := true

-- Test case 5: Small decreasing sequence [5, 4, 3]
def test5_nums : List Int := [5, 4, 3]
def test5_Expected : Bool := false

-- Test case 6: Empty list
def test6_nums : List Int := []
def test6_Expected : Bool := false

-- Test case 7: List with two elements (cannot have triplet)
def test7_nums : List Int := [1, 2]
def test7_Expected : Bool := false

-- Test case 8: List with exactly three equal elements
def test8_nums : List Int := [3, 3, 3]
def test8_Expected : Bool := false

-- Test case 9: Triplet not adjacent [1, 10, 2, 9, 3, 8]
def test9_nums : List Int := [1, 10, 2, 9, 3, 8]
def test9_Expected : Bool := true

-- Test case 10: Single element
def test10_nums : List Int := [5]
def test10_Expected : Bool := false

-- Recommend to validate: 1, 2, 3
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((increasingTriplet test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((increasingTriplet test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((increasingTriplet test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((increasingTriplet test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((increasingTriplet test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((increasingTriplet test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((increasingTriplet test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((increasingTriplet test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((increasingTriplet test9_nums).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((increasingTriplet test10_nums).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 180, Column 0
-- Message: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
--
-- Note: Use `set_option maxHeartbeats <num>` to set the limit.
--
-- Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-- Line: prove_postcondition_decidable_for increasingTriplet
-- [ERROR] Line 180, Column 0
-- Message: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
--
-- Note: Use `set_option maxHeartbeats <num>` to set the limit.
--
-- Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-- Line: prove_postcondition_decidable_for increasingTriplet
-- [ERROR] Line 181, Column 0
-- Message: failed to compile definition, compiler IR check failed at `increasingTripletTester`. Error: depends on declaration 'increasingTripletPostDecidable', which has no executable code; consider marking definition as 'noncomputable'
-- Line: derive_tester_for increasingTriplet
-- [ERROR] Line 182, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
--
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do
-- [ERROR] Line 182, Column 0
-- Message: failed to compile definition, compiler IR check failed at `_private.Init.Data.Range.Basic.0.Std.Range.forIn'.loop._at_._private.Init.Data.Range.Basic.0.Std.Range.forIn'.loop._at_._eval.spec_4.spec_4._redArg._lam_0`. Error: depends on declaration 'increasingTripletTester', which has no executable code; consider marking definition as 'noncomputable'
-- Line: run_elab do

-- extract_program_for increasingTriplet
-- prove_precondition_decidable_for increasingTriplet
-- prove_postcondition_decidable_for increasingTriplet
-- derive_tester_for increasingTriplet
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (List Int)
--     let res := increasingTripletTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break

end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct increasingTriplet by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (nums : List ℤ)
    (a✝¹ : ¬nums.length < 3)
    (b✝ : MProdWithNames ℤ (MProdWithNames Bool (MProdWithNames ℕ (WithName (Option ℤ) (Lean.Name.anonymous.mkStr "second")) (Lean.Name.anonymous.mkStr "i")) (Lean.Name.anonymous.mkStr "found")) (Lean.Name.anonymous.mkStr "first"))
    (a✝ : b✝.snd.snd.fst < nums.length)
    : WPGen (match b✝.snd.snd.snd with | some s => if nums[b✝.snd.snd.fst]! > s then do pure PUnit.unit pure PUnit.unit pure (ForInStep.yield (MProdWithNames.mk' b✝.fst (MProdWithNames.mk' true (MProdWithNames.mk' (b✝.snd.snd.fst + 1) b✝.snd.snd.snd (Lean.Name.anonymous.mkStr "i")) (Lean.Name.anonymous.mkStr "found")) (Lean.Name.anonymous.mkStr "first"))) else if nums[b✝.snd.snd.fst]! ≤ b✝.fst then do pure PUnit.unit pure PUnit.unit pure (ForInStep.yield (MProdWithNames.mk' nums[b✝.snd.snd.fst]! (MProdWithNames.mk' b✝.snd.fst (MProdWithNames.mk' (b✝.snd.snd.fst + 1) b✝.snd.snd.snd (Lean.Name.anonymous.mkStr "i")) (Lean.Name.anonymous.mkStr "found")) (Lean.Name.anonymous.mkStr "first"))) else do pure PUnit.unit pure PUnit.unit pure (ForInStep.yield (MProdWithNames.mk' b✝.fst (MProdWithNames.mk' b✝.snd.fst (MProdWithNames.mk' (b✝.snd.snd.fst + 1) (some nums[b✝.snd.snd.fst]!) (Lean.Name.anonymous.mkStr "i")) (Lean.Name.anonymous.mkStr "found")) (Lean.Name.anonymous.mkStr "first"))) | none => if nums[b✝.snd.snd.fst]! > b✝.fst then do pure PUnit.unit pure PUnit.unit pure (ForInStep.yield (MProdWithNames.mk' b✝.fst (MProdWithNames.mk' b✝.snd.fst (MProdWithNames.mk' (b✝.snd.snd.fst + 1) (some nums[b✝.snd.snd.fst]!) (Lean.Name.anonymous.mkStr "i")) (Lean.Name.anonymous.mkStr "found")) (Lean.Name.anonymous.mkStr "first"))) else do pure PUnit.unit pure PUnit.unit pure (ForInStep.yield (MProdWithNames.mk' nums[b✝.snd.snd.fst]! (MProdWithNames.mk' b✝.snd.fst (MProdWithNames.mk' (b✝.snd.snd.fst + 1) b✝.snd.snd.snd (Lean.Name.anonymous.mkStr "i")) (Lean.Name.anonymous.mkStr "found")) (Lean.Name.anonymous.mkStr "first")))) := by
    sorry



prove_correct increasingTriplet by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 nums a✝¹ b✝ a✝)
end Proof
