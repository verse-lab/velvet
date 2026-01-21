import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def rain_precond (heights : List (Int)) : Prop :=
  -- !benchmark @start precond
  heights.all (fun h => h >= 0)

-- !benchmark @end precond

@[reducible]
def rain_postcond (heights : List (Int)) (result: Int) (h_precond : rain_precond (heights)) : Prop :=
  -- !benchmark @start postcond
  -- The result is the total amount of rainwater trapped by the given terrain
  -- If there are fewer than 3 elements, no water can be trapped
  result >= 0 ∧
  -- The result is non-negative
  if heights.length < 3 then result = 0 else
    -- Water trapped at each position is min(maxLeft, maxRight) - height
    result =
      let max_left_at := λ i =>
        let rec ml (j : Nat) (max_so_far : Int) : Int :=
          if j > i then max_so_far
          else ml (j+1) (max max_so_far (heights[j]!))
          termination_by i + 1 - j
        ml 0 0

      let max_right_at := λ i =>
        let rec mr (j : Nat) (max_so_far : Int) : Int :=
          if j >= heights.length then max_so_far
          else mr (j+1) (max max_so_far (heights[j]!))
          termination_by heights.length - j
        mr i 0

      let water_at := λ i =>
        max 0 (min (max_left_at i) (max_right_at i) - heights[i]!)

      let rec sum_water (i : Nat) (acc : Int) : Int :=
        if i >= heights.length then acc
        else sum_water (i+1) (acc + water_at i)
        termination_by heights.length - i

      sum_water 0 0

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

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

end LeetProofSpec

def precondition_equiv (heights : List (Int)) :
  VerinaSpec.rain_precond heights ↔ LeetProofSpec.precondition heights := by
  sorry

def postcondition_equiv (heights : List (Int)) (result: Int) (h_precond : VerinaSpec.rain_precond (heights)) :
  VerinaSpec.rain_postcond heights result h_precond ↔ LeetProofSpec.postcondition heights result := by
  sorry
