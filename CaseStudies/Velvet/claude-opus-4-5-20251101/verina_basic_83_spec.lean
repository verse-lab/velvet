import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    concat: Concatenate two arrays of integers by appending the second array to the first
    Natural language breakdown:
    1. We have two input arrays a and b, both containing integers
    2. We need to produce a new array that contains all elements from a followed by all elements from b
    3. The length of the result equals the sum of lengths of a and b
    4. For indices 0 to a.size - 1, the result contains elements from a at the same positions
    5. For indices a.size to a.size + b.size - 1, the result contains elements from b
       (specifically, result[a.size + j] = b[j] for j < b.size)
    6. No preconditions are needed since concatenation is always well-defined
    7. Key properties:
       - result.size = a.size + b.size (length property)
       - ∀ i < a.size, result[i] = a[i] (first part matches a)
       - ∀ j < b.size, result[a.size + j] = b[j] (second part matches b)
-/

section Specs

-- Precondition: No restrictions on input arrays
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- Postcondition: Characterizes the concatenated array
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  -- Length property: result length is sum of input lengths
  result.size = a.size + b.size ∧
  -- First part: indices 0 to a.size - 1 match array a
  (∀ i : Nat, i < a.size → result[i]! = a[i]!) ∧
  -- Second part: indices a.size to a.size + b.size - 1 match array b
  (∀ j : Nat, j < b.size → result[a.size + j]! = b[j]!)

end Specs

section Impl

method concat (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic concatenation (example from problem)
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[4, 5]
def test1_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 2: Both arrays empty
def test2_a : Array Int := #[]
def test2_b : Array Int := #[]
def test2_Expected : Array Int := #[]

-- Test case 3: First array has one element, second has multiple
def test3_a : Array Int := #[10]
def test3_b : Array Int := #[20, 30, 40]
def test3_Expected : Array Int := #[10, 20, 30, 40]

-- Test case 4: Arrays with negative numbers
def test4_a : Array Int := #[-1, -2]
def test4_b : Array Int := #[0]
def test4_Expected : Array Int := #[-1, -2, 0]

-- Test case 5: Second array is empty
def test5_a : Array Int := #[7, 8, 9]
def test5_b : Array Int := #[]
def test5_Expected : Array Int := #[7, 8, 9]

-- Test case 6: First array is empty
def test6_a : Array Int := #[]
def test6_b : Array Int := #[100, 200]
def test6_Expected : Array Int := #[100, 200]

-- Test case 7: Single element arrays
def test7_a : Array Int := #[42]
def test7_b : Array Int := #[99]
def test7_Expected : Array Int := #[42, 99]

-- Test case 8: Arrays with duplicate values
def test8_a : Array Int := #[1, 1, 1]
def test8_b : Array Int := #[2, 2]
def test8_Expected : Array Int := #[1, 1, 1, 2, 2]

-- Test case 9: Larger arrays with mixed positive and negative
def test9_a : Array Int := #[-5, 0, 5]
def test9_b : Array Int := #[-10, 10]
def test9_Expected : Array Int := #[-5, 0, 5, -10, 10]

-- Test case 10: Arrays with large values
def test10_a : Array Int := #[1000000, -1000000]
def test10_b : Array Int := #[0]
def test10_Expected : Array Int := #[1000000, -1000000, 0]

-- Recommend to validate: 1, 2, 5

end TestCases
