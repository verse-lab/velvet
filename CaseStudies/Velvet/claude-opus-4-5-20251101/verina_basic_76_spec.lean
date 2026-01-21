import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    myMin: Determine the smaller of two integers
    
    Natural language breakdown:
    1. We are given two integers x and y
    2. We need to return the minimum (smaller) of the two values
    3. If x is less than or equal to y, return x
    4. If x is greater than y, return y
    5. The result must be less than or equal to both inputs
    6. The result must equal one of the two inputs
    7. Lean's built-in `min` function for integers can be used
-/

section Specs

-- Precondition: No restrictions on inputs
def precondition (x : Int) (y : Int) : Prop :=
  True

-- Postcondition: Result is the minimum of x and y
-- Property 1: Result is less than or equal to both inputs
-- Property 2: Result equals one of the inputs
-- Property 3: Result equals min x y (using Lean's built-in min)
def postcondition (x : Int) (y : Int) (result : Int) : Prop :=
  result ≤ x ∧ result ≤ y ∧ (result = x ∨ result = y)

end Specs

section Impl

method myMin (x : Int) (y : Int)
  return (result : Int)
  require precondition x y
  ensures postcondition x y result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: x < y, positive numbers (from problem examples)
def test1_x : Int := 3
def test1_y : Int := 5
def test1_Expected : Int := 3

-- Test case 2: x > y, positive numbers (from problem examples)
def test2_x : Int := 10
def test2_y : Int := 7
def test2_Expected : Int := 7

-- Test case 3: x = y, equal values (from problem examples)
def test3_x : Int := 4
def test3_y : Int := 4
def test3_Expected : Int := 4

-- Test case 4: negative x, y = 0 (from problem examples)
def test4_x : Int := -5
def test4_y : Int := 0
def test4_Expected : Int := -5

-- Test case 5: x = 0, negative y (from problem examples)
def test5_x : Int := 0
def test5_y : Int := -10
def test5_Expected : Int := -10

-- Test case 6: both negative, x < y
def test6_x : Int := -20
def test6_y : Int := -5
def test6_Expected : Int := -20

-- Test case 7: both negative, x > y
def test7_x : Int := -3
def test7_y : Int := -15
def test7_Expected : Int := -15

-- Test case 8: large positive numbers
def test8_x : Int := 1000000
def test8_y : Int := 999999
def test8_Expected : Int := 999999

-- Test case 9: both zero
def test9_x : Int := 0
def test9_y : Int := 0
def test9_Expected : Int := 0

-- Test case 10: positive and negative
def test10_x : Int := 5
def test10_y : Int := -5
def test10_Expected : Int := -5

-- Recommend to validate: 1, 3, 4

end TestCases
