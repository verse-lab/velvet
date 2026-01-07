import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    FilterEven: Filter even numbers from a list using lambda function
    Natural language breakdown:
    1. We have an input list of integers
    2. An integer n is even if and only if n is divisible by 2 (i.e., n % 2 = 0)
    3. We need to extract all even numbers from the input list
    4. The output should contain only the even numbers from the input
    5. The order of elements in the output must match their order in the input (preserve relative ordering)
    6. Each even number should appear in the result exactly as many times as it appears in the input (preserve multiplicity)
    7. If no even numbers exist in the input, return an empty list
    8. An empty input list should return an empty list

    Property-oriented specification:
    Instead of describing the filtering algorithm, we specify the properties that
    the result must satisfy:
    - Every element in the result is even
    - Every element in the result comes from the input
    - Every even element from the input appears in the result with the same count
    - The relative order of elements is preserved
-/

-- Helper Functions

-- Predicate: a number is even if it is divisible by 2

specdef FilterEvenSpec

-- Helper Functions

-- Postcondition clauses
def ensures1 (lst : List Int) (result : List Int) :=
  result.Sublist lst ∧
  ∀ x,
    (x % 2 = 0 → result.count x = lst.count x) ∧
    (x % 2 ≠ 0 → result.count x = 0)


def_pre (lst : List Int) :=
  True  -- no preconditions
def_post (lst : List Int) (result : List Int) :=
  ensures1 lst result

specend FilterEvenSpec

method FilterEven (lst: List Int)
  return (result: List Int)
  require FilterEvenSpec.pre lst
  ensures FilterEvenSpec.post lst result
  do
    sorry

prove_correct FilterEven by sorry

section TestCases

-- Test case 1: Example from problem statement (MUST be first)
def test1_lst : List Int := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def test1_Expected : List Int := [2, 4, 6, 8, 10]

-- Test case 2: All even numbers
def test2_lst : List Int := [2, 4, 6, 8]
def test2_Expected : List Int := [2, 4, 6, 8]

-- Test case 3: All odd numbers
def test3_lst : List Int := [1, 3, 5, 7, 9]
def test3_Expected : List Int := []

-- Test case 4: Empty input
def test4_lst : List Int := []
def test4_Expected : List Int := []

-- Test case 5: Single even number
def test5_lst : List Int := [42]
def test5_Expected : List Int := [42]

-- Test case 6: Single odd number
def test6_lst : List Int := [13]
def test6_Expected : List Int := []

-- Test case 7: Negative numbers (even and odd)
def test7_lst : List Int := [-4, -3, -2, -1, 0, 1, 2]
def test7_Expected : List Int := [-4, -2, 0, 2]

-- Test case 8: Repeated even numbers (test multiplicity preservation)
def test8_lst : List Int := [2, 2, 3, 4, 4, 4]
def test8_Expected : List Int := [2, 2, 4, 4, 4]

-- Test case 9: Large even numbers
def test9_lst : List Int := [100, 101, 200, 201, 300]
def test9_Expected : List Int := [100, 200, 300]

-- Test case 10: Zero (which is even: 0 % 2 = 0)
def test10_lst : List Int := [0]
def test10_Expected : List Int := [0]

-- Test case 11: Mixed positive and negative with zero
def test11_lst : List Int := [-3, -2, -1, 0, 1, 2, 3]
def test11_Expected : List Int := [-2, 0, 2]

-- Test case 12: Large list
def test12_lst : List Int := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
def test12_Expected : List Int := [2, 4, 6, 8, 10, 12, 14, 16, 18, 20]

-- Recommend to validate: test cases 1, 2, 3, 7, 8, 12
-- These cover:
-- - Test 1: Problem statement example (required)
-- - Test 2: All even (boundary case)
-- - Test 3: All odd (empty result)
-- - Test 7: Negative numbers and zero
-- - Test 8: Multiplicity preservation with duplicates
-- - Test 12: Large list with many elements

end TestCases
