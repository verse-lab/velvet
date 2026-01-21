import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    reverse: Reverse an array of integers
    Natural language breakdown:
    1. We have an input array of integers (possibly empty)
    2. The output array must have the same length as the input array
    3. The output array contains the same elements as the input, but in reverse order
    4. For every valid index i, the output at index i equals the input at index (size - 1 - i)
    5. No preconditions needed - works for any array of integers
    6. Edge cases: empty array returns empty, single element returns same element
-/

section Specs

-- Precondition: No restrictions on input array
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: Result is the reverse of input array
-- 1. Same length as input
-- 2. For each index i, result[i] = a[size - 1 - i]
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ∀ i : Nat, i < a.size → result[i]! = a[a.size - 1 - i]!

end Specs

section Impl

method reverse (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Example from problem description - typical case with 5 elements
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Array Int := #[5, 4, 3, 2, 1]

-- Test case 2: Another typical case with 4 elements
def test2_a : Array Int := #[10, 20, 30, 40]
def test2_Expected : Array Int := #[40, 30, 20, 10]

-- Test case 3: Edge case - empty array
def test3_a : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: Edge case - single element
def test4_a : Array Int := #[7]
def test4_Expected : Array Int := #[7]

-- Test case 5: Array with negative numbers and zero
def test5_a : Array Int := #[-1, 0, 1]
def test5_Expected : Array Int := #[1, 0, -1]

-- Test case 6: Array with all same elements
def test6_a : Array Int := #[5, 5, 5, 5]
def test6_Expected : Array Int := #[5, 5, 5, 5]

-- Test case 7: Array with two elements
def test7_a : Array Int := #[100, -100]
def test7_Expected : Array Int := #[-100, 100]

-- Test case 8: Palindrome array (reverse equals original)
def test8_a : Array Int := #[1, 2, 3, 2, 1]
def test8_Expected : Array Int := #[1, 2, 3, 2, 1]

-- Test case 9: Large negative numbers
def test9_a : Array Int := #[-1000, -500, 0, 500, 1000]
def test9_Expected : Array Int := #[1000, 500, 0, -500, -1000]

-- Test case 10: Array with alternating positive and negative
def test10_a : Array Int := #[1, -2, 3, -4]
def test10_Expected : Array Int := #[-4, 3, -2, 1]

-- Recommend to validate: 1, 3, 5

end TestCases
