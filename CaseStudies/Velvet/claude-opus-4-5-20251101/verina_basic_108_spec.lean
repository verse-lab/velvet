import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- below_zero: Compute cumulative sums and check if any goes negative
--
-- Natural language breakdown:
-- 1. Given a list of integers representing sequential operations
-- 2. Generate an array of partial sums where:
--    a. The first element is 0
--    b. Each subsequent element at index i+1 equals element at index i plus operations[i]
-- 3. The resulting array has size = operations.length + 1
-- 4. Return a boolean that is true if any partial sum (at index 1 or later) is negative
-- 5. For empty operations list, return (#[0], false)
-- 6. The partial sum at index i equals the sum of the first i operations

section Specs

-- Helper to compute the sum of the first n elements of a list
def listPrefixSum (ops : List Int) (n : Nat) : Int :=
  (ops.take n).sum

-- Precondition: no constraints on the input list
def precondition (operations : List Int) : Prop :=
  True

-- Postcondition: specifies the properties of the output array and boolean
def postcondition (operations : List Int) (result : Array Int × Bool) : Prop :=
  let arr := result.1
  let hasNegative := result.2
  -- The array size is one more than the operations length
  arr.size = operations.length + 1 ∧
  -- The first element is 0
  arr[0]! = 0 ∧
  -- Each element at index i equals the sum of the first i operations
  (∀ i : Nat, i ≤ operations.length → arr[i]! = listPrefixSum operations i) ∧
  -- The boolean is true iff there exists an index i (1 ≤ i ≤ operations.length) 
  -- such that the partial sum at index i is negative
  (hasNegative = true ↔ ∃ i : Nat, 1 ≤ i ∧ i ≤ operations.length ∧ arr[i]! < 0)

end Specs

section Impl

method below_zero (operations : List Int)
  return (result : Array Int × Bool)
  require precondition operations
  ensures postcondition operations result
  do
  pure (#[0], false)  -- placeholder

end Impl

section TestCases

-- Test case 1: Simple positive operations (example from problem)
def test1_operations : List Int := [1, 2, 3]
def test1_Expected : Array Int × Bool := (#[0, 1, 3, 6], false)

-- Test case 2: Operations with negative value causing negative partial sum
def test2_operations : List Int := [-1, 2, -1]
def test2_Expected : Array Int × Bool := (#[0, -1, 1, 0], true)

-- Test case 3: Empty operations list
def test3_operations : List Int := []
def test3_Expected : Array Int × Bool := (#[0], false)

-- Test case 4: All zeros
def test4_operations : List Int := [0, 0, 0]
def test4_Expected : Array Int × Bool := (#[0, 0, 0, 0], false)

-- Test case 5: Operations causing negative partial sums in middle and end
def test5_operations : List Int := [10, -20, 5]
def test5_Expected : Array Int × Bool := (#[0, 10, -10, -5], true)

-- Test case 6: Single positive operation
def test6_operations : List Int := [5]
def test6_Expected : Array Int × Bool := (#[0, 5], false)

-- Test case 7: Single negative operation
def test7_operations : List Int := [-5]
def test7_Expected : Array Int × Bool := (#[0, -5], true)

-- Test case 8: Large positive then large negative
def test8_operations : List Int := [100, -50, -50]
def test8_Expected : Array Int × Bool := (#[0, 100, 50, 0], false)

-- Test case 9: Multiple negatives causing negative sums
def test9_operations : List Int := [-1, -2, -3]
def test9_Expected : Array Int × Bool := (#[0, -1, -3, -6], true)

-- Test case 10: Alternating positive and negative with no negatives in partial sums
def test10_operations : List Int := [5, -2, 3, -1]
def test10_Expected : Array Int × Bool := (#[0, 5, 3, 6, 5], false)

-- Recommend to validate: 1, 2, 3

end TestCases
