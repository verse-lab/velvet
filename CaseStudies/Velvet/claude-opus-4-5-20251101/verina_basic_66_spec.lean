import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    ComputeIsEven: Determine if a given integer is even
    Natural language breakdown:
    1. We have an input integer x
    2. An integer is even if it is divisible by 2 (i.e., x % 2 = 0)
    3. The function should return true if x is even
    4. The function should return false if x is odd (x % 2 ≠ 0)
    5. The method should work for any integer value (positive, negative, or zero)
    6. Zero is even (0 % 2 = 0)
    7. Negative even numbers (like -2, -4) should return true
    8. Negative odd numbers (like -1, -3) should return false

    Property-oriented specification:
    - The result is true if and only if x modulo 2 equals 0
    - Using Int.emod which is the Euclidean modulo operation
-/

section Specs

-- No helper functions needed - using Int's built-in modulo operation

-- Postcondition: result is true iff x is divisible by 2
def ensures1 (x : Int) (result : Bool) :=
  result = true ↔ x % 2 = 0

def precondition (x : Int) :=
  True  -- no preconditions needed

def postcondition (x : Int) (result : Bool) :=
  ensures1 x result

end Specs

section Impl

method ComputeIsEven (x : Int)
  return (result : Bool)
  require precondition x
  ensures postcondition x result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: Positive even number (from provided tests)
def test1_x : Int := 4
def test1_Expected : Bool := true

-- Test case 2: Positive odd number (from provided tests)
def test2_x : Int := 7
def test2_Expected : Bool := false

-- Test case 3: Zero (edge case - from provided tests)
def test3_x : Int := 0
def test3_Expected : Bool := true

-- Test case 4: Negative even number (from provided tests)
def test4_x : Int := -2
def test4_Expected : Bool := true

-- Test case 5: Negative odd number (from provided tests)
def test5_x : Int := -3
def test5_Expected : Bool := false

-- Test case 6: Positive odd number (small)
def test6_x : Int := 1
def test6_Expected : Bool := false

-- Test case 7: Large positive even number
def test7_x : Int := 100
def test7_Expected : Bool := true

-- Test case 8: Large positive odd number
def test8_x : Int := 99
def test8_Expected : Bool := false

-- Test case 9: Large negative even number
def test9_x : Int := -100
def test9_Expected : Bool := true

-- Test case 10: Negative one (edge case)
def test10_x : Int := -1
def test10_Expected : Bool := false

-- Recommend to validate: 1, 3, 4

end TestCases
