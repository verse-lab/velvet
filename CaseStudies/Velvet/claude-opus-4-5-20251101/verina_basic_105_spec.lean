import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    arrayProduct: Compute the element-wise product of two integer arrays
    Natural language breakdown:
    1. We are given two arrays of integers, a and b
    2. The arrays should be of equal length for the specification to hold
    3. For each index i, we compute the product a[i] * b[i]
    4. The resulting array has the same length as the input arrays
    5. Key properties:
       - The result array has the same size as both input arrays
       - For each valid index i, result[i] = a[i] * b[i]
    6. Edge cases to consider:
       - Arrays with single element
       - Arrays containing zeros (product will be zero)
       - Arrays containing negative numbers
       - Arrays with all same values
-/

section Specs

-- Precondition: arrays must have equal length
def require1 (a : Array Int) (b : Array Int) :=
  a.size = b.size

-- Postcondition clause 1: result has same size as input arrays
def ensures1 (a : Array Int) (b : Array Int) (result : Array Int) :=
  result.size = a.size

-- Postcondition clause 2: each element is the product of corresponding elements
def ensures2 (a : Array Int) (b : Array Int) (result : Array Int) :=
  ∀ i : Nat, i < a.size → result[i]! = a[i]! * b[i]!

def precondition (a : Array Int) (b : Array Int) :=
  require1 a b

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) :=
  ensures1 a b result ∧
  ensures2 a b result

end Specs

section Impl

method arrayProduct (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
    pure #[]

end Impl

section TestCases

-- Test case 1: Basic positive integers (example from problem)
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[4, 5, 6]
def test1_Expected : Array Int := #[4, 10, 18]

-- Test case 2: Array with zeros
def test2_a : Array Int := #[0, 0, 0]
def test2_b : Array Int := #[1, 2, 3]
def test2_Expected : Array Int := #[0, 0, 0]

-- Test case 3: Mixed positive and negative numbers
def test3_a : Array Int := #[-1, 2, -3]
def test3_b : Array Int := #[3, -4, 5]
def test3_Expected : Array Int := #[-3, -8, -15]

-- Test case 4: Single element arrays
def test4_a : Array Int := #[2]
def test4_b : Array Int := #[10]
def test4_Expected : Array Int := #[20]

-- Test case 5: Multiplying by constant array
def test5_a : Array Int := #[1, 2, 3, 4]
def test5_b : Array Int := #[2, 2, 2, 2]
def test5_Expected : Array Int := #[2, 4, 6, 8]

-- Test case 6: Empty arrays
def test6_a : Array Int := #[]
def test6_b : Array Int := #[]
def test6_Expected : Array Int := #[]

-- Test case 7: All negative numbers
def test7_a : Array Int := #[-2, -3, -4]
def test7_b : Array Int := #[-1, -2, -3]
def test7_Expected : Array Int := #[2, 6, 12]

-- Test case 8: Multiplying by ones (identity)
def test8_a : Array Int := #[5, 10, 15]
def test8_b : Array Int := #[1, 1, 1]
def test8_Expected : Array Int := #[5, 10, 15]

-- Test case 9: Large numbers
def test9_a : Array Int := #[100, 200]
def test9_b : Array Int := #[50, 25]
def test9_Expected : Array Int := #[5000, 5000]

-- Test case 10: Zero in middle
def test10_a : Array Int := #[3, 0, 5]
def test10_b : Array Int := #[2, 7, 4]
def test10_Expected : Array Int := #[6, 0, 20]

-- Recommend to validate: 1, 3, 5

end TestCases
