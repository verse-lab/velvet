import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findEvenNumbers: Extract even numbers from an array of integers while preserving order
    Natural language breakdown:
    1. We have an input array of integers
    2. An integer n is even if and only if n is divisible by 2 (i.e., n % 2 = 0)
    3. We need to extract all even numbers from the input array
    4. The output should contain only the even numbers from the input
    5. The order of elements in the output must match their order in the input (preserve relative ordering)
    6. Each even number should appear in the result exactly as many times as it appears in the input
    7. If no even numbers exist in the input, return an empty array
    8. An empty input array should return an empty array
-/

section Specs

-- Helper: check if an integer is even
def isEven (n : Int) : Bool := n % 2 = 0

-- Postcondition clause 1: Every element in result is even
def ensures1 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ i : Nat, i < result.size → isEven (result[i]!) = true

-- Postcondition clause 2: Result is a sublist of the input (preserves order)
def ensures2 (arr : Array Int) (result : Array Int) : Prop :=
  result.toList.Sublist arr.toList

-- Postcondition clause 3: Every even element from input appears in result with same count
def ensures3 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ x : Int, isEven x = true → result.toList.count x = arr.toList.count x

-- Postcondition clause 4: No odd elements in result
def ensures4 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ x : Int, isEven x = false → result.toList.count x = 0

def precondition (arr : Array Int) : Prop :=
  True  -- no preconditions

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  ensures1 arr result ∧
  ensures2 arr result ∧
  ensures3 arr result ∧
  ensures4 arr result

end Specs

section Impl

method findEvenNumbers (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Mixed odd and even numbers (from problem description)
def test1_arr : Array Int := #[1, 2, 3, 4, 5, 6]
def test1_Expected : Array Int := #[2, 4, 6]

-- Test case 2: Another mixed array with larger numbers
def test2_arr : Array Int := #[7, 8, 10, 13, 14]
def test2_Expected : Array Int := #[8, 10, 14]

-- Test case 3: All odd numbers (no even numbers)
def test3_arr : Array Int := #[1, 3, 5, 7]
def test3_Expected : Array Int := #[]

-- Test case 4: Empty array
def test4_arr : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: Array with zero and negative numbers
def test5_arr : Array Int := #[0, -2, -3, -4, 5]
def test5_Expected : Array Int := #[0, -2, -4]

-- Test case 6: All even numbers
def test6_arr : Array Int := #[2, 4, 6, 8, 10]
def test6_Expected : Array Int := #[2, 4, 6, 8, 10]

-- Test case 7: Single even element
def test7_arr : Array Int := #[4]
def test7_Expected : Array Int := #[4]

-- Test case 8: Single odd element
def test8_arr : Array Int := #[3]
def test8_Expected : Array Int := #[]

-- Test case 9: Duplicate even numbers
def test9_arr : Array Int := #[2, 3, 2, 5, 4, 4]
def test9_Expected : Array Int := #[2, 2, 4, 4]

-- Test case 10: Large negative even numbers
def test10_arr : Array Int := #[-100, -99, -98, 0, 1]
def test10_Expected : Array Int := #[-100, -98, 0]

-- Recommend to validate: 1, 3, 5

end TestCases
