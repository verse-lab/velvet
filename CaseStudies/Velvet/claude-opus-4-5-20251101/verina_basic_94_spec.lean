import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    iter_copy: Copy an array to produce an identical array
    Natural language breakdown:
    1. Given an array of integers as input
    2. The output array must have the same size as the input array
    3. Each element in the output array must be identical to the corresponding element in the input array
    4. The order of elements must be preserved
    5. The function works for any array including empty arrays
    6. This is essentially an identity operation on arrays
-/

section Specs

-- Precondition: No special requirements, any array is valid input
def precondition (s : Array Int) : Prop :=
  True

-- Postcondition: The result array is identical to the input array
-- This means same size and same elements at each position
def postcondition (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  ∀ i : Nat, i < s.size → result[i]! = s[i]!

end Specs

section Impl

method iter_copy (s : Array Int)
  return (result : Array Int)
  require precondition s
  ensures postcondition s result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic array with three elements (from problem examples)
def test1_s : Array Int := #[1, 2, 3]
def test1_Expected : Array Int := #[1, 2, 3]

-- Test case 2: Array with four elements
def test2_s : Array Int := #[10, 20, 30, 40]
def test2_Expected : Array Int := #[10, 20, 30, 40]

-- Test case 3: Empty array (edge case)
def test3_s : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: Array with negative numbers
def test4_s : Array Int := #[-1, -2, -3]
def test4_Expected : Array Int := #[-1, -2, -3]

-- Test case 5: Array with repeated elements
def test5_s : Array Int := #[5, 5, 5, 5]
def test5_Expected : Array Int := #[5, 5, 5, 5]

-- Test case 6: Single element array
def test6_s : Array Int := #[42]
def test6_Expected : Array Int := #[42]

-- Test case 7: Array with mixed positive and negative numbers
def test7_s : Array Int := #[-5, 0, 5, -10, 10]
def test7_Expected : Array Int := #[-5, 0, 5, -10, 10]

-- Test case 8: Array with zeros
def test8_s : Array Int := #[0, 0, 0]
def test8_Expected : Array Int := #[0, 0, 0]

-- Test case 9: Large numbers
def test9_s : Array Int := #[1000000, -1000000, 999999]
def test9_Expected : Array Int := #[1000000, -1000000, 999999]

-- Recommend to validate: 1, 3, 5

end TestCases
