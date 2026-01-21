import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    UpdateElements: Update an array by modifying elements at indices 4 and 7
    Natural language breakdown:
    1. We have an array of integers with at least 8 elements
    2. The element at index 4 should be increased by 3
    3. The element at index 7 should be set to 516
    4. All other elements remain unchanged
    5. The result array has the same size as the input array
    6. Indices are 0-indexed
-/

section Specs

-- Precondition: array must have at least 8 elements
def precondition (a : Array Int) : Prop :=
  a.size ≥ 8

-- Postcondition: describes the properties of the result array
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  -- Same size as input
  result.size = a.size ∧
  -- Element at index 4 is original value plus 3
  result[4]! = a[4]! + 3 ∧
  -- Element at index 7 is 516
  result[7]! = 516 ∧
  -- All other elements remain unchanged
  (∀ i : Nat, i < a.size → i ≠ 4 → i ≠ 7 → result[i]! = a[i]!)

end Specs

section Impl

method UpdateElements (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic sequential array (from problem description)
def test1_a : Array Int := #[0, 1, 2, 3, 4, 5, 6, 7, 8]
def test1_Expected : Array Int := #[0, 1, 2, 3, 7, 5, 6, 516, 8]

-- Test case 2: Multiples of 10
def test2_a : Array Int := #[10, 20, 30, 40, 50, 60, 70, 80]
def test2_Expected : Array Int := #[10, 20, 30, 40, 53, 60, 70, 516]

-- Test case 3: Negative numbers
def test3_a : Array Int := #[-1, -2, -3, -4, -5, -6, -7, -8, -9, -10]
def test3_Expected : Array Int := #[-1, -2, -3, -4, -2, -6, -7, 516, -9, -10]

-- Test case 4: All zeros
def test4_a : Array Int := #[0, 0, 0, 0, 0, 0, 0, 0]
def test4_Expected : Array Int := #[0, 0, 0, 0, 3, 0, 0, 516]

-- Test case 5: All same values (5)
def test5_a : Array Int := #[5, 5, 5, 5, 5, 5, 5, 5]
def test5_Expected : Array Int := #[5, 5, 5, 5, 8, 5, 5, 516]

-- Test case 6: Larger array with more elements
def test6_a : Array Int := #[100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]
def test6_Expected : Array Int := #[100, 200, 300, 400, 503, 600, 700, 516, 900, 1000]

-- Test case 7: Array where index 7 already has 516
def test7_a : Array Int := #[1, 2, 3, 4, 5, 6, 7, 516]
def test7_Expected : Array Int := #[1, 2, 3, 4, 8, 6, 7, 516]

-- Test case 8: Edge case with minimum size (exactly 8 elements)
def test8_a : Array Int := #[0, 0, 0, 0, -3, 0, 0, 0]
def test8_Expected : Array Int := #[0, 0, 0, 0, 0, 0, 0, 516]

-- Test case 9: Mixed positive and negative
def test9_a : Array Int := #[1, -1, 2, -2, 3, -3, 4, -4, 5]
def test9_Expected : Array Int := #[1, -1, 2, -2, 6, -3, 4, 516, 5]

-- Test case 10: Large values
def test10_a : Array Int := #[1000000, 2000000, 3000000, 4000000, 5000000, 6000000, 7000000, 8000000]
def test10_Expected : Array Int := #[1000000, 2000000, 3000000, 4000000, 5000003, 6000000, 7000000, 516]

-- Recommend to validate: 1, 2, 4

end TestCases
