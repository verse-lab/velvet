import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    maxOfThree: Find the maximum among three given integers
    Natural language breakdown:
    1. We are given three integers a, b, and c
    2. We need to find and return the maximum value among these three integers
    3. The result must be greater than or equal to each of the input numbers
    4. The result must equal one of the input values (a, b, or c)
    5. These two properties together uniquely determine the maximum
    6. No preconditions are needed - any three integers are valid input
-/

section Specs

-- Postcondition clause 1: result is greater than or equal to all inputs
def ensures1 (a : Int) (b : Int) (c : Int) (result : Int) :=
  result ≥ a ∧ result ≥ b ∧ result ≥ c

-- Postcondition clause 2: result is one of the input values
def ensures2 (a : Int) (b : Int) (c : Int) (result : Int) :=
  result = a ∨ result = b ∨ result = c

def precondition (a : Int) (b : Int) (c : Int) :=
  True  -- no preconditions needed for any three integers

def postcondition (a : Int) (b : Int) (c : Int) (result : Int) :=
  ensures1 a b c result ∧
  ensures2 a b c result

end Specs

section Impl

method maxOfThree (a : Int) (b : Int) (c : Int)
  return (result : Int)
  require precondition a b c
  ensures postcondition a b c result
  do
  pure 0  -- placeholder

end Impl

section TestCases

-- Test case 1: a is the maximum (from problem examples)
def test1_a : Int := 3
def test1_b : Int := 2
def test1_c : Int := 1
def test1_Expected : Int := 3

-- Test case 2: all values are equal
def test2_a : Int := 5
def test2_b : Int := 5
def test2_c : Int := 5
def test2_Expected : Int := 5

-- Test case 3: b is the maximum
def test3_a : Int := 10
def test3_b : Int := 20
def test3_c : Int := 15
def test3_Expected : Int := 20

-- Test case 4: all negative values, a is maximum
def test4_a : Int := -1
def test4_b : Int := -2
def test4_c : Int := -3
def test4_Expected : Int := -1

-- Test case 5: mix of zero and negative, a is maximum
def test5_a : Int := 0
def test5_b : Int := -10
def test5_c : Int := -5
def test5_Expected : Int := 0

-- Test case 6: c is the maximum
def test6_a : Int := 1
def test6_b : Int := 2
def test6_c : Int := 7
def test6_Expected : Int := 7

-- Test case 7: two values tied for maximum (a and b)
def test7_a : Int := 10
def test7_b : Int := 10
def test7_c : Int := 5
def test7_Expected : Int := 10

-- Test case 8: large positive and negative values
def test8_a : Int := -1000
def test8_b : Int := 1000
def test8_c : Int := 0
def test8_Expected : Int := 1000

-- Test case 9: a and c tied for maximum
def test9_a : Int := 42
def test9_b : Int := 10
def test9_c : Int := 42
def test9_Expected : Int := 42

-- Test case 10: descending order b > c > a
def test10_a : Int := -5
def test10_b : Int := 100
def test10_c : Int := 50
def test10_Expected : Int := 100

-- Recommend to validate: 1, 3, 4

end TestCases
