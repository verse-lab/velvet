import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    double_array_elements: Transform an array of integers by doubling each element
    Natural language breakdown:
    1. We are given an array of integers as input
    2. We need to produce an output array where each element is doubled (multiplied by 2)
    3. The output array must have the same size as the input array
    4. For each valid index i, the element at position i in the result equals twice the element at position i in the input
    5. Edge cases:
       - Empty array: returns empty array
       - Single element array: returns array with that element doubled
       - Arrays with negative numbers: negative numbers are doubled correctly (e.g., -3 becomes -6)
       - Arrays with zero: zero doubled is still zero
-/

section Specs

-- Precondition: no special requirements on the input array
def precondition (s : Array Int) : Prop :=
  True

-- Postcondition: result has same size and each element is doubled
def postcondition (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  ∀ i : Nat, i < s.size → result[i]! = 2 * s[i]!

end Specs

section Impl

method double_array_elements (s : Array Int)
  return (result : Array Int)
  require precondition s
  ensures postcondition s result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Empty array (edge case)
def test1_s : Array Int := #[]
def test1_Expected : Array Int := #[]

-- Test case 2: Typical array with positive integers
def test2_s : Array Int := #[1, 2, 3, 4, 5]
def test2_Expected : Array Int := #[2, 4, 6, 8, 10]

-- Test case 3: Array with zero and negative numbers
def test3_s : Array Int := #[0, -1, 5]
def test3_Expected : Array Int := #[0, -2, 10]

-- Test case 4: Single element array
def test4_s : Array Int := #[100]
def test4_Expected : Array Int := #[200]

-- Test case 5: Array with only negative numbers
def test5_s : Array Int := #[-3, -4]
def test5_Expected : Array Int := #[-6, -8]

-- Test case 6: Array with all zeros
def test6_s : Array Int := #[0, 0, 0]
def test6_Expected : Array Int := #[0, 0, 0]

-- Test case 7: Array with mixed positive, negative, and zero
def test7_s : Array Int := #[-5, 0, 7, -2, 3]
def test7_Expected : Array Int := #[-10, 0, 14, -4, 6]

-- Test case 8: Array with large numbers
def test8_s : Array Int := #[1000000, -1000000]
def test8_Expected : Array Int := #[2000000, -2000000]

-- Test case 9: Single negative element
def test9_s : Array Int := #[-7]
def test9_Expected : Array Int := #[-14]

-- Test case 10: Single zero element
def test10_s : Array Int := #[0]
def test10_Expected : Array Int := #[0]

-- Recommend to validate: 1, 2, 3

end TestCases
