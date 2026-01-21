import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
--   Rain: Calculate how much rainwater can be trapped by a terrain represented as an array of heights
--   Natural language breakdown:
--   1. Given a list of non-negative integers representing elevation levels (terrain heights)
--   2. Each bar has width 1 unit, and the height is given by the list value
--   3. Water can be trapped between higher elevation points on both sides
--   4. For each position i, water can be trapped if there exists a higher bar to the left AND right
--   5. The water level at position i is determined by the minimum of:
--      - the maximum height among all bars at positions 0..i (inclusive)
--      - the maximum height among all bars at positions i..end (inclusive)
--   6. Water trapped at position i = max(0, water_level_i - height_i)
--   7. Total trapped water is the sum of water at each position
--   8. Edge cases:
--      - Empty list: no water trapped (result = 0)
--      - Single element: no water trapped (result = 0)
--      - Two elements: no water trapped (result = 0)
--      - Flat terrain: no water trapped (result = 0)
--      - Monotonic sequences: no water trapped (result = 0)
--   9. Key properties:
--      - All heights must be non-negative
--      - Result must be non-negative
--      - Water at each position is bounded by heights on both sides

section Specs

-- Helper: maximum of a list with default 0
def listMax (l : List Int) : Int :=
  l.foldl max 0

-- Helper: maximum height from index 0 to i (inclusive)
def maxLeft (heights : List Int) (i : Nat) : Int :=
  listMax (heights.take (i + 1))

-- Helper: maximum height from index i to end (inclusive)
def maxRight (heights : List Int) (i : Nat) : Int :=
  listMax (heights.drop i)

-- Helper: water trapped at a specific position
def waterAt (heights : List Int) (i : Nat) : Int :=
  let leftMax := maxLeft heights i
  let rightMax := maxRight heights i
  let waterLevel := min leftMax rightMax
  max (waterLevel - heights[i]!) 0

-- Precondition: all heights are non-negative
def allNonNegative (heights : List Int) : Prop :=
  ∀ i : Nat, i < heights.length → heights[i]! ≥ 0

def precondition (heights : List Int) :=
  allNonNegative heights

-- Postcondition: result equals the total trapped water
-- Water at each position i is: max(0, min(maxLeft, maxRight) - height[i])
-- Total water is the sum over all positions
def postcondition (heights : List Int) (result : Int) :=
  result = ((List.range heights.length).map (waterAt heights)).foldl (· + ·) 0

end Specs

section Impl

method rain (heights : List Int)
  return (result : Int)
  require precondition heights
  ensures postcondition heights result
  do
    pure 0

end Impl

section TestCases

-- Test case 1: Example from problem description
def test1_heights : List Int := [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]
def test1_Expected : Int := 6

-- Test case 2: Another example from problem
def test2_heights : List Int := [4, 2, 0, 3, 2, 5]
def test2_Expected : Int := 9

-- Test case 3: Flat terrain - no water trapped
def test3_heights : List Int := [1, 1, 1]
def test3_Expected : Int := 0

-- Test case 4: Two elements - no water trapped
def test4_heights : List Int := [10, 5]
def test4_Expected : Int := 0

-- Test case 5: Small valley
def test5_heights : List Int := [1, 10, 9, 11]
def test5_Expected : Int := 1

-- Test case 6: Empty list
def test6_heights : List Int := []
def test6_Expected : Int := 0

-- Test case 7: Single element
def test7_heights : List Int := [5]
def test7_Expected : Int := 0

-- Test case 8: Monotonically increasing - no water trapped
def test8_heights : List Int := [1, 2, 3, 4, 5]
def test8_Expected : Int := 0

-- Test case 9: Monotonically decreasing - no water trapped
def test9_heights : List Int := [5, 4, 3, 2, 1]
def test9_Expected : Int := 0

-- Test case 10: Simple valley
def test10_heights : List Int := [3, 0, 3]
def test10_Expected : Int := 3

-- Recommend to validate: 1, 2, 5

end TestCases
