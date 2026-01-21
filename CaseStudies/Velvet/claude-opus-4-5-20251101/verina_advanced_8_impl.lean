import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    canCompleteCircuit: Determine if a circular journey around gas stations is possible
    Natural language breakdown:
    1. We have n gas stations arranged in a circle
    2. Each station i provides gas[i] amount of gas
    3. Traveling from station i to station (i+1) mod n costs cost[i] gas
    4. We start with an empty tank at some station
    5. We need to find the smallest index of a starting station that allows completing the circuit
    6. At no point during the journey can the tank go negative
    7. If no valid starting station exists, return -1
    8. Key insight: A valid starting station exists iff total gas >= total cost
    9. For a starting station s to be valid:
       - Starting with 0 gas at station s
       - At each station k (visited in order s, s+1, ..., s+n-1 mod n):
         * We add gas[k mod n] to our tank
         * We subtract cost[k mod n] to travel to next station
         * The tank must never go negative at any step
-/

section Specs
register_specdef_allow_recursion

-- Helper: compute running tank level after visiting k stations starting from station start
-- Returns the tank level after leaving station (start + k - 1) mod n for k > 0
def tankAfterSteps (gas : List Int) (cost : List Int) (start : Nat) (steps : Nat) : Int :=
  match steps with
  | 0 => 0
  | k + 1 =>
    let prev := tankAfterSteps gas cost start k
    let idx := (start + k) % gas.length
    prev + gas[idx]! - cost[idx]!

-- Helper: check if starting from station s allows completing the entire circuit
-- Tank must be non-negative after each step (after refueling and traveling)
def canCompleteFrom (gas : List Int) (cost : List Int) (start : Nat) : Prop :=
  ∀ k : Nat, k < gas.length → tankAfterSteps gas cost start (k + 1) ≥ 0

-- Helper: check if a given index is a valid solution (can complete circuit from there)
def isValidStart (gas : List Int) (cost : List Int) (idx : Nat) : Prop :=
  idx < gas.length ∧ canCompleteFrom gas cost idx

-- Precondition: gas and cost arrays have equal non-zero length
def require1 (gas : List Int) (cost : List Int) :=
  gas.length > 0

def require2 (gas : List Int) (cost : List Int) :=
  gas.length = cost.length

def precondition (gas : List Int) (cost : List Int) :=
  require1 gas cost ∧ require2 gas cost

-- Postcondition: result is -1 if no solution exists, otherwise smallest valid starting index
def ensures1 (gas : List Int) (cost : List Int) (result : Int) :=
  result = -1 ∨ (result ≥ 0 ∧ result < gas.length)

-- If result >= 0, it must be a valid starting station
def ensures2 (gas : List Int) (cost : List Int) (result : Int) :=
  result ≥ 0 → isValidStart gas cost result.toNat

-- If result >= 0, it must be the smallest valid starting station
def ensures3 (gas : List Int) (cost : List Int) (result : Int) :=
  result ≥ 0 → ∀ j : Nat, j < result.toNat → ¬isValidStart gas cost j

-- If result = -1, no valid starting station exists
def ensures4 (gas : List Int) (cost : List Int) (result : Int) :=
  result = -1 → ∀ j : Nat, j < gas.length → ¬canCompleteFrom gas cost j

def postcondition (gas : List Int) (cost : List Int) (result : Int) :=
  ensures1 gas cost result ∧
  ensures2 gas cost result ∧
  ensures3 gas cost result ∧
  ensures4 gas cost result
end Specs

section Impl
method canCompleteCircuit (gas : List Int) (cost : List Int)
  return (result : Int)
  require precondition gas cost
  ensures postcondition gas cost result
  do
  let n := gas.length
  let mut start := 0
  let mut found := false
  let mut answer : Int := -1
  while start < n
    -- Bounds on start
    invariant "start_lower" 0 ≤ start
    invariant "start_upper" start ≤ n
    -- n equals gas.length
    invariant "n_def" n = gas.length
    -- found and answer are consistent
    invariant "answer_found_consistency" (found = false → answer = -1)
    invariant "answer_found_true" (found = true → answer ≥ 0 ∧ answer < n)
    -- If found is true, answer is a valid starting station
    invariant "found_valid" (found = true → isValidStart gas cost answer.toNat)
    -- If found is true, answer is the smallest valid start in [0, start)
    invariant "found_smallest" (found = true → ∀ j : Nat, j < answer.toNat → ¬isValidStart gas cost j)
    -- If found is false, no valid start exists in [0, start)
    invariant "not_found_checked" (found = false → ∀ j : Nat, j < start → ¬canCompleteFrom gas cost j)
    done_with (start = n ∨ found = true)
  do
    -- Try to complete the circuit starting from 'start'
    let mut tank : Int := 0
    let mut i := 0
    let mut valid := true
    while i < n
      -- Bounds on i
      invariant "i_lower" 0 ≤ i
      invariant "i_upper" i ≤ n
      -- n equals gas.length
      invariant "n_def_inner" n = gas.length
      -- tank equals cumulative sum after i steps
      invariant "tank_def" tank = tankAfterSteps gas cost start i
      -- valid tracks whether all intermediate tanks were non-negative
      invariant "valid_meaning" (valid = true → ∀ k : Nat, k < i → tankAfterSteps gas cost start (k + 1) ≥ 0)
      -- If valid is false, there exists some step where tank went negative
      invariant "invalid_meaning" (valid = false → ∃ k : Nat, k < i ∧ tankAfterSteps gas cost start (k + 1) < 0)
      -- start is still valid
      invariant "start_bound_inner" start < n
      done_with (i = n ∨ valid = false)
    do
      let idx := (start + i) % n
      tank := tank + gas[idx]! - cost[idx]!
      if tank < 0 then
        valid := false
      i := i + 1
    -- Check if this starting position works
    if valid then
      found := true
      answer := start
      break
    start := start + 1
  return answer
end Impl

section TestCases
-- Test case 1: Standard case with valid solution at index 3
def test1_gas : List Int := [1, 2, 3, 4, 5]
def test1_cost : List Int := [3, 4, 5, 1, 2]
def test1_Expected : Int := 3

-- Test case 2: No valid starting station exists
def test2_gas : List Int := [2, 3, 4]
def test2_cost : List Int := [3, 4, 3]
def test2_Expected : Int := -1

-- Test case 3: Valid solution at index 4
def test3_gas : List Int := [5, 1, 2, 3, 4]
def test3_cost : List Int := [4, 4, 1, 5, 1]
def test3_Expected : Int := 4

-- Test case 4: No valid starting station
def test4_gas : List Int := [3, 3, 4]
def test4_cost : List Int := [3, 4, 4]
def test4_Expected : Int := -1

-- Test case 5: Perfect balance, solution at index 0
def test5_gas : List Int := [1, 2, 3]
def test5_cost : List Int := [1, 2, 3]
def test5_Expected : Int := 0

-- Test case 6: Multiple valid starts, return smallest (index 1)
def test6_gas : List Int := [1, 2, 3, 4]
def test6_cost : List Int := [2, 2, 2, 2]
def test6_Expected : Int := 1

-- Test case 7: All zeros for gas, cannot complete
def test7_gas : List Int := [0, 0, 0]
def test7_cost : List Int := [1, 1, 1]
def test7_Expected : Int := -1

-- Recommend to validate: 1, 2, 5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((canCompleteCircuit test1_gas test1_cost).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((canCompleteCircuit test2_gas test2_cost).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((canCompleteCircuit test3_gas test3_cost).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((canCompleteCircuit test4_gas test4_cost).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((canCompleteCircuit test5_gas test5_cost).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((canCompleteCircuit test6_gas test6_cost).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((canCompleteCircuit test7_gas test7_cost).run), DivM.res test7_Expected ]
end Assertions

section Pbt
extract_program_for canCompleteCircuit
prove_precondition_decidable_for canCompleteCircuit
prove_postcondition_decidable_for canCompleteCircuit
derive_tester_for canCompleteCircuit
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (List Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (List Int)
    let res := canCompleteCircuitTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct canCompleteCircuit by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (gas : List ℤ)
    (cost : List ℤ)
    (require_1 : precondition gas cost)
    (answer : ℤ)
    (found : Bool)
    (start : ℕ)
    (invariant_start_upper : start ≤ gas.length)
    (invariant_answer_found_consistency : found = false → answer = -1)
    (invariant_found_valid : found = true → isValidStart gas cost answer.toNat)
    (invariant_not_found_checked : found = false → ∀ j < start, ¬canCompleteFrom gas cost j)
    (if_pos : start < gas.length)
    (i : ℕ)
    (tank : ℤ)
    (valid : Bool)
    (invariant_i_upper : i ≤ gas.length)
    (invariant_tank_def : tank = tankAfterSteps gas cost start i)
    (invariant_invalid_meaning : valid = false → ∃ k < i, tankAfterSteps gas cost start (k + 1) < 0)
    (invariant_start_bound_inner : start < gas.length)
    (if_pos_1 : i < gas.length)
    (invariant_start_lower : True)
    (invariant_answer_found_true : found = true → 0 ≤ answer ∧ answer < ↑gas.length)
    (invariant_found_smallest : found = true → ∀ (j : ℕ), ↑j < answer → ¬isValidStart gas cost j)
    (invariant_i_lower : True)
    (invariant_valid_meaning : valid = true → ∀ k < i, 0 ≤ tankAfterSteps gas cost start (k + 1))
    (if_pos_2 : tank + gas[(start + i) % gas.length]?.getD 0 < cost[(start + i) % gas.length]?.getD 0)
    : tank + gas[(start + i) % gas.length]?.getD 0 - cost[(start + i) % gas.length]?.getD 0 = tankAfterSteps gas cost start (i + 1) := by
    -- Get that gas.length > 0 from precondition
    have h_len_pos : gas.length > 0 := require_1.1
    have h_len_eq : gas.length = cost.length := require_1.2
    -- The index is valid
    have h_idx_valid : (start + i) % gas.length < gas.length := Nat.mod_lt (start + i) h_len_pos
    have h_idx_valid_cost : (start + i) % gas.length < cost.length := by rw [← h_len_eq]; exact h_idx_valid
    -- Rewrite getElem? to some (getElem) using the valid index
    have h_gas_getElem : gas[(start + i) % gas.length]? = some (gas[(start + i) % gas.length]) := 
      List.getElem?_eq_getElem h_idx_valid
    have h_cost_getElem : cost[(start + i) % gas.length]? = some (cost[(start + i) % gas.length]) := 
      List.getElem?_eq_getElem h_idx_valid_cost
    -- Now simplify getD of some
    have h_gas_eq : gas[(start + i) % gas.length]?.getD 0 = gas[(start + i) % gas.length] := by
      rw [h_gas_getElem, Option.getD_some]
    have h_cost_eq : cost[(start + i) % gas.length]?.getD 0 = cost[(start + i) % gas.length] := by
      rw [h_cost_getElem, Option.getD_some]
    -- Now unfold tankAfterSteps for (i + 1) and use invariant
    rw [h_gas_eq, h_cost_eq]
    -- Unfold the RHS
    conv_rhs => unfold tankAfterSteps
    -- Use the tank invariant
    rw [invariant_tank_def]
    -- The getElem! should match getElem when index is valid
    simp only [List.getElem!_eq_getElem?_getD, h_gas_getElem, h_cost_getElem, Option.getD_some]

theorem goal_1
    (gas : List ℤ)
    (cost : List ℤ)
    (require_1 : precondition gas cost)
    (answer : ℤ)
    (found : Bool)
    (start : ℕ)
    (invariant_start_upper : start ≤ gas.length)
    (invariant_answer_found_consistency : found = false → answer = -1)
    (invariant_found_valid : found = true → isValidStart gas cost answer.toNat)
    (invariant_not_found_checked : found = false → ∀ j < start, ¬canCompleteFrom gas cost j)
    (if_pos : start < gas.length)
    (i : ℕ)
    (tank : ℤ)
    (valid : Bool)
    (invariant_i_upper : i ≤ gas.length)
    (invariant_tank_def : tank = tankAfterSteps gas cost start i)
    (invariant_invalid_meaning : valid = false → ∃ k < i, tankAfterSteps gas cost start (k + 1) < 0)
    (invariant_start_bound_inner : start < gas.length)
    (if_pos_1 : i < gas.length)
    (invariant_start_lower : True)
    (invariant_answer_found_true : found = true → 0 ≤ answer ∧ answer < ↑gas.length)
    (invariant_found_smallest : found = true → ∀ (j : ℕ), ↑j < answer → ¬isValidStart gas cost j)
    (invariant_i_lower : True)
    (invariant_valid_meaning : valid = true → ∀ k < i, 0 ≤ tankAfterSteps gas cost start (k + 1))
    (if_pos_2 : tank + gas[(start + i) % gas.length]?.getD 0 < cost[(start + i) % gas.length]?.getD 0)
    : ∃ k < i + 1, tankAfterSteps gas cost start (k + 1) < 0 := by
    use i
    constructor
    · exact Nat.lt_succ_self i
    · -- Need to show tankAfterSteps gas cost start (i + 1) < 0
      -- First, unfold the definition
      unfold tankAfterSteps
      simp only
      -- tankAfterSteps gas cost start (i + 1) = tankAfterSteps gas cost start i + gas[idx]! - cost[idx]!
      rw [← invariant_tank_def]
      -- Now need to show: tank + gas[(start + i) % gas.length]! - cost[(start + i) % gas.length]! < 0
      have h_len : gas.length > 0 := require_1.1
      have h_eq : gas.length = cost.length := require_1.2
      have h_idx : (start + i) % gas.length < gas.length := Nat.mod_lt _ h_len
      have h_idx_cost : (start + i) % gas.length < cost.length := by omega
      -- Use getElem!_eq_getElem?_getD to convert
      simp only [List.getElem!_eq_getElem?_getD]
      -- Now both sides use getElem?.getD
      -- The goal should be: tank + gas[...]?.getD default - cost[...]?.getD default < 0
      -- We need to show the getD expressions match
      have hg : gas[(start + i) % gas.length]?.getD (default : ℤ) = gas[(start + i) % gas.length]?.getD 0 := by
        rw [List.getElem?_eq_getElem h_idx]
        simp [Option.getD_some]
      have hc : cost[(start + i) % gas.length]?.getD (default : ℤ) = cost[(start + i) % gas.length]?.getD 0 := by
        rw [List.getElem?_eq_getElem h_idx_cost]
        simp [Option.getD_some]
      rw [hg, hc]
      omega

theorem goal_2
    (gas : List ℤ)
    (cost : List ℤ)
    (require_1 : precondition gas cost)
    (answer : ℤ)
    (found : Bool)
    (start : ℕ)
    (invariant_start_upper : start ≤ gas.length)
    (invariant_answer_found_consistency : found = false → answer = -1)
    (invariant_found_valid : found = true → isValidStart gas cost answer.toNat)
    (invariant_not_found_checked : found = false → ∀ j < start, ¬canCompleteFrom gas cost j)
    (if_pos : start < gas.length)
    (i : ℕ)
    (tank : ℤ)
    (valid : Bool)
    (invariant_i_upper : i ≤ gas.length)
    (invariant_tank_def : tank = tankAfterSteps gas cost start i)
    (invariant_invalid_meaning : valid = false → ∃ k < i, tankAfterSteps gas cost start (k + 1) < 0)
    (invariant_start_bound_inner : start < gas.length)
    (if_pos_1 : i < gas.length)
    (invariant_start_lower : True)
    (invariant_answer_found_true : found = true → 0 ≤ answer ∧ answer < ↑gas.length)
    (invariant_found_smallest : found = true → ∀ (j : ℕ), ↑j < answer → ¬isValidStart gas cost j)
    (invariant_i_lower : True)
    (invariant_valid_meaning : valid = true → ∀ k < i, 0 ≤ tankAfterSteps gas cost start (k + 1))
    (if_neg : cost[(start + i) % gas.length]?.getD 0 ≤ tank + gas[(start + i) % gas.length]?.getD 0)
    : tank + gas[(start + i) % gas.length]?.getD 0 - cost[(start + i) % gas.length]?.getD 0 = tankAfterSteps gas cost start (i + 1) := by
    unfold tankAfterSteps
    simp only [Nat.add_eq, Nat.add_zero]
    rw [invariant_tank_def]
    have h_len_pos : gas.length > 0 := require_1.1
    have h_idx_lt : (start + i) % gas.length < gas.length := Nat.mod_lt (start + i) h_len_pos
    have h_cost_len : cost.length = gas.length := require_1.2.symm
    have h_idx_lt_cost : (start + i) % gas.length < cost.length := by omega
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem h_idx_lt, List.getElem?_eq_getElem h_idx_lt_cost]
    simp only [Option.getD_some]

theorem goal_3
    (gas : List ℤ)
    (cost : List ℤ)
    (require_1 : precondition gas cost)
    (answer : ℤ)
    (found : Bool)
    (start : ℕ)
    (invariant_start_upper : start ≤ gas.length)
    (invariant_answer_found_consistency : found = false → answer = -1)
    (invariant_found_valid : found = true → isValidStart gas cost answer.toNat)
    (invariant_not_found_checked : found = false → ∀ j < start, ¬canCompleteFrom gas cost j)
    (if_pos : start < gas.length)
    (i : ℕ)
    (tank : ℤ)
    (valid : Bool)
    (invariant_i_upper : i ≤ gas.length)
    (invariant_tank_def : tank = tankAfterSteps gas cost start i)
    (invariant_invalid_meaning : valid = false → ∃ k < i, tankAfterSteps gas cost start (k + 1) < 0)
    (invariant_start_bound_inner : start < gas.length)
    (if_pos_1 : i < gas.length)
    (invariant_start_lower : True)
    (invariant_answer_found_true : found = true → 0 ≤ answer ∧ answer < ↑gas.length)
    (invariant_found_smallest : found = true → ∀ (j : ℕ), ↑j < answer → ¬isValidStart gas cost j)
    (invariant_i_lower : True)
    (invariant_valid_meaning : valid = true → ∀ k < i, 0 ≤ tankAfterSteps gas cost start (k + 1))
    (if_neg : cost[(start + i) % gas.length]?.getD 0 ≤ tank + gas[(start + i) % gas.length]?.getD 0)
    : valid = true → ∀ k < i + 1, 0 ≤ tankAfterSteps gas cost start (k + 1) := by
    intro hvalid k hk
    have hle : k ≤ i := Nat.lt_succ_iff.mp hk
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · -- Case k < i: use invariant_valid_meaning
      exact invariant_valid_meaning hvalid k hlt
    · -- Case k = i: use if_neg to show the new tank level is non-negative
      subst heq
      -- We need to show 0 ≤ tankAfterSteps gas cost start (i + 1)
      -- First unfold the definition
      unfold tankAfterSteps
      simp only
      -- Now we have: tankAfterSteps gas cost start i + gas[idx]! - cost[idx]!
      -- From invariant_tank_def: tank = tankAfterSteps gas cost start i
      -- From if_neg: cost[idx]?.getD 0 ≤ tank + gas[idx]?.getD 0
      -- So: tank + gas[idx]?.getD 0 - cost[idx]?.getD 0 ≥ 0
      have hlen : gas.length > 0 := require_1.1
      have idx_lt : (start + k) % gas.length < gas.length := Nat.mod_lt _ hlen
      have hcost_len : cost.length = gas.length := require_1.2.symm
      have idx_lt_cost : (start + k) % gas.length < cost.length := by omega
      rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
      have h1 : gas[(start + k) % gas.length]? = some gas[(start + k) % gas.length] := List.getElem?_eq_getElem idx_lt
      have h2 : cost[(start + k) % gas.length]? = some cost[(start + k) % gas.length] := List.getElem?_eq_getElem idx_lt_cost
      simp only [h1, h2, Option.getD_some]
      have h3 : gas[(start + k) % gas.length]?.getD 0 = gas[(start + k) % gas.length] := by simp [h1]
      have h4 : cost[(start + k) % gas.length]?.getD 0 = cost[(start + k) % gas.length] := by simp [h2]
      -- Note: after subst, invariant_tank_def becomes: tank = tankAfterSteps gas cost start k
      -- and if_neg becomes: cost[(start + k) % gas.length]?.getD 0 ≤ tank + gas[(start + k) % gas.length]?.getD 0
      rw [← h3, ← h4, ← invariant_tank_def]
      omega

theorem goal_4
    (gas : List ℤ)
    (cost : List ℤ)
    (require_1 : precondition gas cost)
    (answer : ℤ)
    (found : Bool)
    (start : ℕ)
    (invariant_start_upper : start ≤ gas.length)
    (invariant_answer_found_consistency : found = false → answer = -1)
    (invariant_found_valid : found = true → isValidStart gas cost answer.toNat)
    (invariant_not_found_checked : found = false → ∀ j < start, ¬canCompleteFrom gas cost j)
    (if_pos : start < gas.length)
    (invariant_start_lower : True)
    (invariant_answer_found_true : found = true → 0 ≤ answer ∧ answer < ↑gas.length)
    (invariant_found_smallest : found = true → ∀ (j : ℕ), ↑j < answer → ¬isValidStart gas cost j)
    : 0 = tankAfterSteps gas cost start 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_5
    (gas : List ℤ)
    (cost : List ℤ)
    (require_1 : precondition gas cost)
    (answer : ℤ)
    (found : Bool)
    (start : ℕ)
    (invariant_start_upper : start ≤ gas.length)
    (invariant_answer_found_consistency : found = false → answer = -1)
    (invariant_found_valid : found = true → isValidStart gas cost answer.toNat)
    (invariant_not_found_checked : found = false → ∀ j < start, ¬canCompleteFrom gas cost j)
    (if_pos : start < gas.length)
    (i : ℕ)
    (tank : ℤ)
    (valid : Bool)
    (invariant_i_upper : i ≤ gas.length)
    (invariant_tank_def : tank = tankAfterSteps gas cost start i)
    (invariant_invalid_meaning : valid = false → ∃ k < i, tankAfterSteps gas cost start (k + 1) < 0)
    (invariant_start_bound_inner : start < gas.length)
    (done_2 : i = gas.length ∨ valid = false)
    (i_1 : ℕ)
    (i_2 : ℤ)
    (valid_1 : Bool)
    (if_pos_1 : valid_1 = true)
    (invariant_start_lower : True)
    (invariant_answer_found_true : found = true → 0 ≤ answer ∧ answer < ↑gas.length)
    (invariant_found_smallest : found = true → ∀ (j : ℕ), ↑j < answer → ¬isValidStart gas cost j)
    (invariant_i_lower : True)
    (invariant_valid_meaning : valid = true → ∀ k < i, 0 ≤ tankAfterSteps gas cost start (k + 1))
    (i_3 : i = i_1 ∧ tank = i_2 ∧ valid = valid_1)
    : isValidStart gas cost start := by
  -- Extract that valid = valid_1 from i_3
  obtain ⟨_, _, h_valid_eq⟩ := i_3
  -- Since valid_1 = true and valid = valid_1, we have valid = true
  have h_valid_true : valid = true := by rw [h_valid_eq]; exact if_pos_1
  -- From done_2 and valid = true, we get i = gas.length
  have h_i_eq : i = gas.length := by
    cases done_2 with
    | inl h => exact h
    | inr h => 
      rw [h_valid_true] at h
      exact absurd rfl (ne_true_of_eq_false h)
  -- Get the validity condition for all k < i (= gas.length)
  have h_all_valid := invariant_valid_meaning h_valid_true
  -- Prove canCompleteFrom
  have h_can_complete : canCompleteFrom gas cost start := by
    unfold canCompleteFrom
    intro k hk
    rw [← h_i_eq] at hk
    exact h_all_valid k hk
  -- Combine with start < gas.length to get isValidStart
  unfold isValidStart
  exact ⟨if_pos, h_can_complete⟩

theorem goal_7
    (gas : List ℤ)
    (cost : List ℤ)
    (require_1 : precondition gas cost)
    (answer : ℤ)
    (found : Bool)
    (start : ℕ)
    (invariant_start_upper : start ≤ gas.length)
    (invariant_answer_found_consistency : found = false → answer = -1)
    (invariant_found_valid : found = true → isValidStart gas cost answer.toNat)
    (invariant_not_found_checked : found = false → ∀ j < start, ¬canCompleteFrom gas cost j)
    (if_pos : start < gas.length)
    (i : ℕ)
    (tank : ℤ)
    (valid : Bool)
    (invariant_i_upper : i ≤ gas.length)
    (invariant_tank_def : tank = tankAfterSteps gas cost start i)
    (invariant_invalid_meaning : valid = false → ∃ k < i, tankAfterSteps gas cost start (k + 1) < 0)
    (invariant_start_bound_inner : start < gas.length)
    (done_2 : i = gas.length ∨ valid = false)
    (i_1 : ℕ)
    (i_2 : ℤ)
    (valid_1 : Bool)
    (invariant_start_lower : True)
    (invariant_answer_found_true : found = true → 0 ≤ answer ∧ answer < ↑gas.length)
    (invariant_found_smallest : found = true → ∀ (j : ℕ), ↑j < answer → ¬isValidStart gas cost j)
    (invariant_i_lower : True)
    (invariant_valid_meaning : valid = true → ∀ k < i, 0 ≤ tankAfterSteps gas cost start (k + 1))
    (i_3 : i = i_1 ∧ tank = i_2 ∧ valid = valid_1)
    (if_neg : valid_1 = false)
    : found = false → ∀ j < start + 1, ¬canCompleteFrom gas cost j := by
    intro hfound j hj
    -- j < start + 1 means j ≤ start
    rw [Nat.lt_succ_iff] at hj
    -- Case split: j < start or j = start
    cases Nat.lt_or_eq_of_le hj with
    | inl hlt =>
      -- j < start: use invariant_not_found_checked
      exact invariant_not_found_checked hfound j hlt
    | inr heq =>
      -- j = start: show start cannot complete the circuit
      subst heq
      -- From i_3, we have valid = valid_1 = false
      have hvalid : valid = false := by
        obtain ⟨_, _, hv⟩ := i_3
        rw [hv, if_neg]
      -- From invariant_invalid_meaning, there exists k < i where tank went negative
      obtain ⟨k, hki, hneg⟩ := invariant_invalid_meaning hvalid
      -- Show canCompleteFrom gas cost start is false
      intro hcan
      -- canCompleteFrom means all tank levels are non-negative
      unfold canCompleteFrom at hcan
      -- k < i ≤ gas.length, so k < gas.length
      have hk_lt : k < gas.length := Nat.lt_of_lt_of_le hki invariant_i_upper
      -- Apply hcan to k
      have hpos := hcan k hk_lt
      -- But we have tankAfterSteps gas cost start (k + 1) < 0
      omega

theorem goal_8
    (gas : List ℤ)
    (cost : List ℤ)
    (require_1 : precondition gas cost)
    (answer : ℤ)
    (found : Bool)
    (start : ℕ)
    (invariant_start_upper : start ≤ gas.length)
    (invariant_answer_found_consistency : found = false → answer = -1)
    (invariant_found_valid : found = true → isValidStart gas cost answer.toNat)
    (invariant_not_found_checked : found = false → ∀ j < start, ¬canCompleteFrom gas cost j)
    (done_1 : start = gas.length ∨ found = true)
    (i : ℤ)
    (i_1 : Bool)
    (start_1 : ℕ)
    (invariant_start_lower : True)
    (invariant_answer_found_true : found = true → 0 ≤ answer ∧ answer < ↑gas.length)
    (invariant_found_smallest : found = true → ∀ (j : ℕ), ↑j < answer → ¬isValidStart gas cost j)
    (i_2 : answer = i ∧ found = i_1 ∧ start = start_1)
    : postcondition gas cost i := by
  obtain ⟨hi, _, _⟩ := i_2
  subst hi
  unfold postcondition ensures1 ensures2 ensures3 ensures4
  cases hf : found with
  | false =>
    have hans : answer = -1 := invariant_answer_found_consistency hf
    refine ⟨Or.inl hans, ?_, ?_, ?_⟩
    · intro hge
      rw [hans] at hge
      omega
    · intro hge
      rw [hans] at hge
      omega
    · intro _
      intro j hj
      cases done_1 with
      | inl hstart =>
        have hchecked := invariant_not_found_checked hf
        rw [hstart] at hchecked
        exact hchecked j hj
      | inr hfound =>
        rw [hf] at hfound
        contradiction
  | true =>
    have hvalid := invariant_found_valid hf
    have hbounds := invariant_answer_found_true hf
    have hsmallest := invariant_found_smallest hf
    refine ⟨Or.inr ⟨hbounds.1, hbounds.2⟩, ?_, ?_, ?_⟩
    · intro _
      unfold isValidStart at hvalid ⊢
      have h0 : 0 ≤ answer := hbounds.1
      have htonat_eq : answer.toNat = answer.toNat := rfl
      exact hvalid
    · intro _
      intro j hj
      have hlt : (j : ℤ) < answer := by
        have h0 : 0 ≤ answer := hbounds.1
        omega
      exact hsmallest j hlt
    · intro heq
      have h0 : 0 ≤ answer := hbounds.1
      omega

theorem goal_6
    (gas : List ℤ)
    (cost : List ℤ)
    (require_1 : precondition gas cost)
    (answer : ℤ)
    (found : Bool)
    (start : ℕ)
    (invariant_start_upper : start ≤ gas.length)
    (invariant_answer_found_consistency : found = false → answer = -1)
    (invariant_found_valid : found = true → isValidStart gas cost answer.toNat)
    (invariant_not_found_checked : found = false → ∀ j < start, ¬canCompleteFrom gas cost j)
    (if_pos : start < gas.length)
    (i : ℕ)
    (tank : ℤ)
    (valid : Bool)
    (invariant_i_upper : i ≤ gas.length)
    (invariant_tank_def : tank = tankAfterSteps gas cost start i)
    (invariant_invalid_meaning : valid = false → ∃ k < i, tankAfterSteps gas cost start (k + 1) < 0)
    (invariant_start_bound_inner : start < gas.length)
    (done_2 : i = gas.length ∨ valid = false)
    (i_1 : ℕ)
    (i_2 : ℤ)
    (valid_1 : Bool)
    (if_pos_1 : valid_1 = true)
    (invariant_start_lower : True)
    (invariant_answer_found_true : found = true → 0 ≤ answer ∧ answer < ↑gas.length)
    (invariant_found_smallest : found = true → ∀ (j : ℕ), ↑j < answer → ¬isValidStart gas cost j)
    (invariant_i_lower : True)
    (invariant_valid_meaning : valid = true → ∀ k < i, 0 ≤ tankAfterSteps gas cost start (k + 1))
    (i_3 : i = i_1 ∧ tank = i_2 ∧ valid = valid_1)
    : ∀ j < start, ¬isValidStart gas cost j := by
    sorry



prove_correct canCompleteCircuit by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 gas cost require_1 answer found start invariant_start_upper invariant_answer_found_consistency invariant_found_valid invariant_not_found_checked if_pos i tank valid invariant_i_upper invariant_tank_def invariant_invalid_meaning invariant_start_bound_inner if_pos_1 invariant_start_lower invariant_answer_found_true invariant_found_smallest invariant_i_lower invariant_valid_meaning if_pos_2)
  exact (goal_1 gas cost require_1 answer found start invariant_start_upper invariant_answer_found_consistency invariant_found_valid invariant_not_found_checked if_pos i tank valid invariant_i_upper invariant_tank_def invariant_invalid_meaning invariant_start_bound_inner if_pos_1 invariant_start_lower invariant_answer_found_true invariant_found_smallest invariant_i_lower invariant_valid_meaning if_pos_2)
  exact (goal_2 gas cost require_1 answer found start invariant_start_upper invariant_answer_found_consistency invariant_found_valid invariant_not_found_checked if_pos i tank valid invariant_i_upper invariant_tank_def invariant_invalid_meaning invariant_start_bound_inner if_pos_1 invariant_start_lower invariant_answer_found_true invariant_found_smallest invariant_i_lower invariant_valid_meaning if_neg)
  exact (goal_3 gas cost require_1 answer found start invariant_start_upper invariant_answer_found_consistency invariant_found_valid invariant_not_found_checked if_pos i tank valid invariant_i_upper invariant_tank_def invariant_invalid_meaning invariant_start_bound_inner if_pos_1 invariant_start_lower invariant_answer_found_true invariant_found_smallest invariant_i_lower invariant_valid_meaning if_neg)
  exact (goal_4 gas cost require_1 answer found start invariant_start_upper invariant_answer_found_consistency invariant_found_valid invariant_not_found_checked if_pos invariant_start_lower invariant_answer_found_true invariant_found_smallest)
  exact (goal_5 gas cost require_1 answer found start invariant_start_upper invariant_answer_found_consistency invariant_found_valid invariant_not_found_checked if_pos i tank valid invariant_i_upper invariant_tank_def invariant_invalid_meaning invariant_start_bound_inner done_2 i_1 i_2 valid_1 if_pos_1 invariant_start_lower invariant_answer_found_true invariant_found_smallest invariant_i_lower invariant_valid_meaning i_3)
  exact (goal_6 gas cost require_1 answer found start invariant_start_upper invariant_answer_found_consistency invariant_found_valid invariant_not_found_checked if_pos i tank valid invariant_i_upper invariant_tank_def invariant_invalid_meaning invariant_start_bound_inner done_2 i_1 i_2 valid_1 if_pos_1 invariant_start_lower invariant_answer_found_true invariant_found_smallest invariant_i_lower invariant_valid_meaning i_3)
  exact (goal_7 gas cost require_1 answer found start invariant_start_upper invariant_answer_found_consistency invariant_found_valid invariant_not_found_checked if_pos i tank valid invariant_i_upper invariant_tank_def invariant_invalid_meaning invariant_start_bound_inner done_2 i_1 i_2 valid_1 invariant_start_lower invariant_answer_found_true invariant_found_smallest invariant_i_lower invariant_valid_meaning i_3 if_neg)
  exact (goal_8 gas cost require_1 answer found start invariant_start_upper invariant_answer_found_consistency invariant_found_valid invariant_not_found_checked done_1 i i_1 start_1 invariant_start_lower invariant_answer_found_true invariant_found_smallest i_2)
end Proof
