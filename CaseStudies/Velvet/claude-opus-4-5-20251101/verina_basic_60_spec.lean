import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    FindEvenNumbers: Filter even numbers from an array preserving order
    Natural language breakdown:
    1. We have an input array of integers
    2. An integer n is even if and only if n % 2 = 0 (using Int.even_iff from Mathlib)
    3. We need to extract all even numbers from the input array
    4. The output should contain only the even numbers from the input
    5. The order of elements in the output must match their order in the input (preserve relative ordering)
    6. Each even number should appear in the result exactly as many times as it appears in the input (preserve multiplicity)
    7. If no even numbers exist in the input, return an empty array
    8. An empty input array should return an empty array

    Property-oriented specification:
    Instead of describing the filtering algorithm, we specify the properties that
    the result must satisfy:
    - The result is a sublist of the input (preserves order)
    - Every element in the result is even
    - Every even element from the input appears in the result with the same count
    - Every odd element has count 0 in the result
-/

section Specs

-- Helper function: check if an integer is even
def isEven (n : Int) : Prop := n % 2 = 0

-- Postcondition clause 1: result is a sublist of input (preserves order)
def ensures1 (arr : Array Int) (result : Array Int) : Prop :=
  result.toList.Sublist arr.toList

-- Postcondition clause 2: all elements in result are even
def ensures2 (result : Array Int) : Prop :=
  ∀ i : Nat, i < result.size → result[i]! % 2 = 0

-- Postcondition clause 3: count preservation for even elements
def ensures3 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ x : Int, x % 2 = 0 → result.toList.count x = arr.toList.count x

-- Postcondition clause 4: odd elements have count 0 in result
def ensures4 (result : Array Int) : Prop :=
  ∀ x : Int, x % 2 ≠ 0 → result.toList.count x = 0

def precondition (arr : Array Int) : Prop :=
  True  -- no preconditions

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  ensures1 arr result ∧
  ensures2 result ∧
  ensures3 arr result ∧
  ensures4 result

end Specs

section Impl

method FindEvenNumbers (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Mixed array with positive integers (example from problem)
def test1_arr : Array Int := #[1, 2, 3, 4, 5, 6]
def test1_Expected : Array Int := #[2, 4, 6]

-- Test case 2: Array with zero and negative numbers
def test2_arr : Array Int := #[0, -2, 3, -4, 7]
def test2_Expected : Array Int := #[0, -2, -4]

-- Test case 3: Array with all odd numbers
def test3_arr : Array Int := #[1, 3, 5, 7]
def test3_Expected : Array Int := #[]

-- Test case 4: Array with all even numbers
def test4_arr : Array Int := #[2, 4, 8, 10]
def test4_Expected : Array Int := #[2, 4, 8, 10]

-- Test case 5: Empty array
def test5_arr : Array Int := #[]
def test5_Expected : Array Int := #[]

-- Test case 6: Array with duplicate even numbers
def test6_arr : Array Int := #[2, 4, 2, 6]
def test6_Expected : Array Int := #[2, 4, 2, 6]

-- Test case 7: Mixed array with duplicates
def test7_arr : Array Int := #[1, 2, 8, 2, 5]
def test7_Expected : Array Int := #[2, 8, 2]

-- Test case 8: Single even element
def test8_arr : Array Int := #[4]
def test8_Expected : Array Int := #[4]

-- Test case 9: Single odd element
def test9_arr : Array Int := #[3]
def test9_Expected : Array Int := #[]

-- Test case 10: Large negative even numbers
def test10_arr : Array Int := #[-100, -99, -98, 0, 1]
def test10_Expected : Array Int := #[-100, -98, 0]

-- Recommend to validate: 1, 2, 5

end TestCases
