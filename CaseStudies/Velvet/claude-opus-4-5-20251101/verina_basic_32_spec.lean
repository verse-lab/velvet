import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    swapFirstAndLast: Swap the first and last elements of an array of integers
    Natural language breakdown:
    1. We have a non-empty array of integers as input
    2. The output is a new array of the same size
    3. The first element of the output is the last element of the input
    4. The last element of the output is the first element of the input
    5. All other elements (indices 1 to size-2) remain unchanged in their positions
    6. Edge case: Single element array returns the same array (first = last)
    7. Edge case: Two element array swaps both elements
-/

section Specs

-- Precondition: Array must be non-empty
def precondition (a : Array Int) : Prop :=
  a.size ≥ 1

-- Postcondition: Describes the swapped array properties
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  -- Same size as input
  result.size = a.size ∧
  -- First element of result is last element of input
  result[0]! = a[a.size - 1]! ∧
  -- Last element of result is first element of input
  result[result.size - 1]! = a[0]! ∧
  -- All middle elements remain unchanged
  (∀ i : Nat, 0 < i → i < a.size - 1 → result[i]! = a[i]!)

end Specs

section Impl

method swapFirstAndLast (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  pure #[0]  -- placeholder

end Impl

section TestCases

-- Test case 1: Standard array with 5 elements (example from problem)
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Array Int := #[5, 2, 3, 4, 1]

-- Test case 2: Single element array (edge case - first = last)
def test2_a : Array Int := #[10]
def test2_Expected : Array Int := #[10]

-- Test case 3: Two element array (simple swap)
def test3_a : Array Int := #[1, 2]
def test3_Expected : Array Int := #[2, 1]

-- Test case 4: Three element array
def test4_a : Array Int := #[1, 2, 3]
def test4_Expected : Array Int := #[3, 2, 1]

-- Test case 5: Array with negative numbers
def test5_a : Array Int := #[-5, 0, 10, -3]
def test5_Expected : Array Int := #[-3, 0, 10, -5]

-- Test case 6: Array with duplicate first and last
def test6_a : Array Int := #[7, 2, 3, 7]
def test6_Expected : Array Int := #[7, 2, 3, 7]

-- Test case 7: Array with all same elements
def test7_a : Array Int := #[5, 5, 5, 5, 5]
def test7_Expected : Array Int := #[5, 5, 5, 5, 5]

-- Test case 8: Large numbers
def test8_a : Array Int := #[1000000, 2, 3, -1000000]
def test8_Expected : Array Int := #[-1000000, 2, 3, 1000000]

-- Test case 9: Array with zero at boundaries
def test9_a : Array Int := #[0, 1, 2, 3, 0]
def test9_Expected : Array Int := #[0, 1, 2, 3, 0]

-- Test case 10: Longer array
def test10_a : Array Int := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def test10_Expected : Array Int := #[10, 2, 3, 4, 5, 6, 7, 8, 9, 1]

-- Recommend to validate: 1, 2, 3

end TestCases
