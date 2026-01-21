import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    trapRainWater: Calculate how much water can be trapped between elevations after rain
    Natural language breakdown:
    1. Given a list of non-negative integers representing an elevation map
    2. For each position i, water can be trapped based on surrounding elevations
    3. Water at position i is bounded by the minimum of:
       - The maximum height among all positions from 0 to i (inclusive)
       - The maximum height among all positions from i to the end (inclusive)
    4. Water trapped at position i = (water level at i) - height[i], if positive
    5. Total water = sum of water trapped at each position
    6. Edge cases: empty list or list with fewer than 3 elements traps 0 water
    7. Ascending or descending sequences trap 0 water (no valleys)
-/

section Specs

-- Helper: maximum value among positions 0 to i (inclusive) in the list
-- This represents the highest barrier on the left side including position i
def leftMax (height : List Nat) (i : Nat) : Nat :=
  (height.take (i + 1)).foldl max 0

-- Helper: maximum value among positions i to end (inclusive) in the list
-- This represents the highest barrier on the right side including position i
def rightMax (height : List Nat) (i : Nat) : Nat :=
  (height.drop i).foldl max 0

-- Precondition: no special requirements (empty list is valid)
def precondition (height : List Nat) :=
  True

-- Postcondition: result equals the total trapped water
-- Water at each position i is determined by:
--   waterLevel(i) = min(leftMax(i), rightMax(i))
--   trapped(i) = waterLevel(i) - height[i] (if positive, else 0)
-- The result is the sum over all positions
def postcondition (height : List Nat) (result : Nat) :=
  result = (Finset.range height.length).sum (fun i =>
    let waterLevel := min (leftMax height i) (rightMax height i)
    let h := if i < height.length then height[i]! else 0
    if waterLevel > h then waterLevel - h else 0)

end Specs

section Impl

method trapRainWater (height : List Nat)
  return (result : Nat)
  require precondition height
  ensures postcondition height result
  do
    pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - complex elevation with valleys
def test1_height : List Nat := [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]
def test1_Expected : Nat := 6

-- Test case 2: Another example from problem
def test2_height : List Nat := [4, 2, 0, 3, 2, 5]
def test2_Expected : Nat := 9

-- Test case 3: Simple valley with three elements
def test3_height : List Nat := [1, 0, 2]
def test3_Expected : Nat := 1

-- Test case 4: Multiple valleys
def test4_height : List Nat := [3, 0, 1, 3, 0, 5]
def test4_Expected : Nat := 8

-- Test case 5: Ascending sequence (no water trapped)
def test5_height : List Nat := [0, 1, 2, 3, 4, 5]
def test5_Expected : Nat := 0

-- Test case 6: Empty list
def test6_height : List Nat := []
def test6_Expected : Nat := 0

-- Test case 7: Descending sequence (no water trapped)
def test7_height : List Nat := [5, 4, 3, 2, 1, 0]
def test7_Expected : Nat := 0

-- Test case 8: Single element
def test8_height : List Nat := [5]
def test8_Expected : Nat := 0

-- Test case 9: Two elements (no valley possible)
def test9_height : List Nat := [2, 4]
def test9_Expected : Nat := 0

-- Test case 10: Flat terrain
def test10_height : List Nat := [3, 3, 3, 3]
def test10_Expected : Nat := 0

-- Recommend to validate: 1, 2, 3

end TestCases
