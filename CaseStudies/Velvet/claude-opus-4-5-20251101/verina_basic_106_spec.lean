import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    arraySum: Compute the element-wise sum of two integer arrays
    Natural language breakdown:
    1. We have two input arrays of integers, a and b
    2. Both input arrays must have the same length (precondition)
    3. The result is a new array where each element at index i is the sum of a[i] and b[i]
    4. The resulting array has the same size as the input arrays
    5. Edge cases to consider:
       - Empty arrays: result should be empty array
       - Single element arrays: result has one element which is the sum
       - Arrays with negative numbers: normal integer addition applies
       - Arrays with zeros: 0 + x = x
    6. Key properties:
       - Result size equals input size
       - For each valid index i, result[i] = a[i] + b[i]
-/

section Specs

-- Precondition: both arrays must have the same size
def precondition (a : Array Int) (b : Array Int) :=
  a.size = b.size

-- Postcondition: result has same size and element-wise sum property
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) :=
  result.size = a.size ∧
  ∀ i : Nat, i < a.size → result[i]! = a[i]! + b[i]!

end Specs

section Impl

method arraySum (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic example from problem (positive integers)
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[4, 5, 6]
def test1_Expected : Array Int := #[5, 7, 9]

-- Test case 2: All zeros
def test2_a : Array Int := #[0, 0, 0]
def test2_b : Array Int := #[0, 0, 0]
def test2_Expected : Array Int := #[0, 0, 0]

-- Test case 3: Mixed positive and negative integers
def test3_a : Array Int := #[-1, 2, 3]
def test3_b : Array Int := #[1, -2, 4]
def test3_Expected : Array Int := #[0, 0, 7]

-- Test case 4: Single element arrays with cancellation
def test4_a : Array Int := #[10]
def test4_b : Array Int := #[-10]
def test4_Expected : Array Int := #[0]

-- Test case 5: Larger numbers
def test5_a : Array Int := #[100, 200, 300]
def test5_b : Array Int := #[100, 200, 300]
def test5_Expected : Array Int := #[200, 400, 600]

-- Test case 6: Empty arrays
def test6_a : Array Int := #[]
def test6_b : Array Int := #[]
def test6_Expected : Array Int := #[]

-- Test case 7: Negative numbers only
def test7_a : Array Int := #[-5, -10, -15]
def test7_b : Array Int := #[-1, -2, -3]
def test7_Expected : Array Int := #[-6, -12, -18]

-- Test case 8: One array all zeros
def test8_a : Array Int := #[7, 8, 9]
def test8_b : Array Int := #[0, 0, 0]
def test8_Expected : Array Int := #[7, 8, 9]

-- Test case 9: Large array
def test9_a : Array Int := #[1, 2, 3, 4, 5]
def test9_b : Array Int := #[5, 4, 3, 2, 1]
def test9_Expected : Array Int := #[6, 6, 6, 6, 6]

-- Test case 10: Single positive element
def test10_a : Array Int := #[42]
def test10_b : Array Int := #[58]
def test10_Expected : Array Int := #[100]

-- Recommend to validate: 1, 3, 6

end TestCases
