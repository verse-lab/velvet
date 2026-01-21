import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    myMin: Determine the minimum of two integers
    Natural language breakdown:
    1. We have two integers a and b as input
    2. We need to return the smaller of the two numbers
    3. The result must be less than or equal to both inputs
    4. The result must be equal to either a or b (it is one of the inputs)
    5. When both numbers are equal, the result equals both (either can be returned)
    6. This is equivalent to the standard min function on integers
-/

section Specs

-- Precondition: No restrictions on the inputs
def precondition (a : Int) (b : Int) :=
  True

-- Postcondition clauses:
-- 1. The result is less than or equal to a
def ensures1 (a : Int) (b : Int) (result : Int) :=
  result ≤ a

-- 2. The result is less than or equal to b
def ensures2 (a : Int) (b : Int) (result : Int) :=
  result ≤ b

-- 3. The result is one of the two inputs
def ensures3 (a : Int) (b : Int) (result : Int) :=
  result = a ∨ result = b

def postcondition (a : Int) (b : Int) (result : Int) :=
  ensures1 a b result ∧ ensures2 a b result ∧ ensures3 a b result

end Specs

section Impl

method myMin (a : Int) (b : Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure (min a b)

end Impl

section TestCases

-- Test case 1: Basic case where first is smaller
def test1_a : Int := 3
def test1_b : Int := 5
def test1_Expected : Int := 3

-- Test case 2: Basic case where second is smaller
def test2_a : Int := 10
def test2_b : Int := 7
def test2_Expected : Int := 7

-- Test case 3: Both numbers are equal
def test3_a : Int := 4
def test3_b : Int := 4
def test3_Expected : Int := 4

-- Test case 4: First is negative, second is positive
def test4_a : Int := -3
def test4_b : Int := 5
def test4_Expected : Int := -3

-- Test case 5: First is positive, second is negative
def test5_a : Int := 3
def test5_b : Int := -5
def test5_Expected : Int := -5

-- Test case 6: Both are negative
def test6_a : Int := -3
def test6_b : Int := -5
def test6_Expected : Int := -5

-- Test case 7: First is zero, second is positive
def test7_a : Int := 0
def test7_b : Int := 10
def test7_Expected : Int := 0

-- Test case 8: First is zero, second is negative
def test8_a : Int := 0
def test8_b : Int := -10
def test8_Expected : Int := -10

-- Recommend to validate: 1, 4, 6

end TestCases
