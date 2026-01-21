import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    moveZeroes: Move all zeroes in a list to the end while preserving relative order of non-zero elements
    Natural language breakdown:
    1. Given a list of integers xs
    2. The result should contain all elements from xs (same multiset - each element appears same number of times)
    3. All non-zero elements should appear before all zero elements in the result
    4. The relative order of non-zero elements must be preserved (they appear in same order as in input)
    5. The number of zeroes in the result equals the number of zeroes in the input
-/

section Specs

-- Helper Functions

-- Get non-zero elements preserving order (used for specifying relative order preservation)
def nonZeroElements (xs : List Int) : List Int :=
  xs.filter (· ≠ 0)

-- Postcondition clauses

-- Every element appears the same number of times in result as in input (implies same length)
def ensures1 (xs : List Int) (result : List Int) :=
  ∀ x : Int, result.count x = xs.count x

-- All non-zero elements come before all zero elements
-- If position i has a zero and position j > i, then position j must also have a zero
def ensures2 (xs : List Int) (result : List Int) :=
  ∀ i j : Nat, i < j → j < result.length → result[i]! = 0 → result[j]! = 0

-- The non-zero elements in the result preserve their relative order from input
-- This is captured by: the subsequence of non-zeros in result equals the subsequence of non-zeros in input
def ensures3 (xs : List Int) (result : List Int) :=
  nonZeroElements result = nonZeroElements xs

def precondition (xs : List Int) :=
  True  -- no preconditions

def postcondition (xs : List Int) (result : List Int) :=
  ensures1 xs result ∧ ensures2 xs result ∧ ensures3 xs result

end Specs

section Impl

method moveZeroes (xs : List Int)
  return (result : List Int)
  require precondition xs
  ensures postcondition xs result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Example from problem - mixed zeroes and non-zeroes
def test1_xs : List Int := [0, 1, 0, 3, 12]
def test1_Expected : List Int := [1, 3, 12, 0, 0]

-- Test case 2: Zeroes at the beginning
def test2_xs : List Int := [0, 0, 1]
def test2_Expected : List Int := [1, 0, 0]

-- Test case 3: No zeroes in list
def test3_xs : List Int := [1, 2, 3]
def test3_Expected : List Int := [1, 2, 3]

-- Test case 4: All zeroes
def test4_xs : List Int := [0, 0, 0]
def test4_Expected : List Int := [0, 0, 0]

-- Test case 5: Empty list
def test5_xs : List Int := []
def test5_Expected : List Int := []

-- Test case 6: Zeroes interspersed
def test6_xs : List Int := [4, 0, 5, 0, 6]
def test6_Expected : List Int := [4, 5, 6, 0, 0]

-- Test case 7: Single zero followed by non-zero
def test7_xs : List Int := [0, 1]
def test7_Expected : List Int := [1, 0]

-- Test case 8: Non-zero followed by single zero
def test8_xs : List Int := [1, 0]
def test8_Expected : List Int := [1, 0]

-- Test case 9: Multiple zeroes in middle
def test9_xs : List Int := [2, 0, 0, 3]
def test9_Expected : List Int := [2, 3, 0, 0]

-- Recommend to validate: 1, 3, 6

end TestCases
