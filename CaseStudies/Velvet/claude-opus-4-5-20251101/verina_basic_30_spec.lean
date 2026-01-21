import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    elementWiseModulo: Compute element-wise modulo between two arrays of integers
    Natural language breakdown:
    1. Given two arrays of integers a and b of the same length
    2. Produce a new array where each element is the remainder of dividing the corresponding element from a by the element from b
    3. The modulo operation for integers follows Lean's Int.emod semantics
    4. Preconditions:
       - Both arrays must have the same length
       - All elements in the second array must be non-zero (to avoid division by zero)
    5. Postconditions:
       - The resulting array has the same length as the input arrays
       - Each element at index i in the result equals a[i] % b[i] (element-wise modulo)
    6. Edge cases:
       - Empty arrays: result is an empty array
       - Arrays with negative numbers: uses Lean's Int.emod behavior
       - Cases where a[i] is divisible by b[i]: result element is 0
-/

section Specs

-- Precondition: arrays have same length and all elements in b are non-zero
def require1 (a : Array Int) (b : Array Int) :=
  a.size = b.size

def require2 (a : Array Int) (b : Array Int) :=
  ∀ i : Nat, i < b.size → b[i]! ≠ 0

-- Postcondition: result has same length as inputs
def ensures1 (a : Array Int) (b : Array Int) (result : Array Int) :=
  result.size = a.size

-- Postcondition: each element is the modulo of corresponding elements
def ensures2 (a : Array Int) (b : Array Int) (result : Array Int) :=
  ∀ i : Nat, i < a.size → result[i]! = a[i]! % b[i]!

def precondition (a : Array Int) (b : Array Int) :=
  require1 a b ∧ require2 a b

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) :=
  ensures1 a b result ∧ ensures2 a b result

end Specs

section Impl

method elementWiseModulo (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic example from problem description
def test1_a : Array Int := #[10, 20, 30]
def test1_b : Array Int := #[3, 7, 5]
def test1_Expected : Array Int := #[1, 6, 0]

-- Test case 2: All divisible (result all zeros)
def test2_a : Array Int := #[100, 200, 300, 400]
def test2_b : Array Int := #[10, 20, 30, 50]
def test2_Expected : Array Int := #[0, 0, 0, 0]

-- Test case 3: Negative numbers (Lean's emod behavior)
def test3_a : Array Int := #[-10, -20, 30]
def test3_b : Array Int := #[3, -7, 5]
def test3_Expected : Array Int := #[2, 1, 0]

-- Test case 4: Empty arrays
def test4_a : Array Int := #[]
def test4_b : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: Single element arrays
def test5_a : Array Int := #[17]
def test5_b : Array Int := #[5]
def test5_Expected : Array Int := #[2]

-- Test case 6: Modulo with divisor larger than dividend
def test6_a : Array Int := #[3, 5, 7]
def test6_b : Array Int := #[10, 10, 10]
def test6_Expected : Array Int := #[3, 5, 7]

-- Test case 7: Mixed positive and negative results
def test7_a : Array Int := #[-15, 15, -15, 15]
def test7_b : Array Int := #[4, 4, -4, -4]
def test7_Expected : Array Int := #[1, 3, 1, 3]

-- Test case 8: Large numbers
def test8_a : Array Int := #[1000000, 999999]
def test8_b : Array Int := #[7, 13]
def test8_Expected : Array Int := #[6, 12]

-- Test case 9: All ones as divisors
def test9_a : Array Int := #[5, -3, 0, 7]
def test9_b : Array Int := #[1, 1, 1, 1]
def test9_Expected : Array Int := #[0, 0, 0, 0]

-- Test case 10: Dividend equals divisor
def test10_a : Array Int := #[5, -5, 7]
def test10_b : Array Int := #[5, -5, 7]
def test10_Expected : Array Int := #[0, 0, 0]

-- Recommend to validate: 1, 3, 5

end TestCases
