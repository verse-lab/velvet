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
  pure (-1)  -- placeholder

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
