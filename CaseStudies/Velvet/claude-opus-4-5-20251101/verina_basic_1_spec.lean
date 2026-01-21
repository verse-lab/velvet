import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    hasOppositeSign: Determine whether two given integers have opposite signs
    Natural language breakdown:
    1. We have two input integers a and b
    2. An integer is positive if it is greater than zero
    3. An integer is negative if it is less than zero
    4. Zero is considered neither positive nor negative
    5. Two integers have opposite signs if one is positive and the other is negative
    6. If either integer is zero, the result should be false
    7. The function returns true if (a > 0 and b < 0) or (a < 0 and b > 0)
    8. The function returns false otherwise (both non-negative, both non-positive, or either is zero)

    Property-oriented specification:
    - Using Int.sign: sign(a) returns 1 for positive, -1 for negative, 0 for zero
    - Two integers have opposite signs iff sign(a) * sign(b) = -1
    - Equivalently: result = true iff (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)
-/

section Specs

-- Precondition: no restrictions on input integers
def precondition (a : Int) (b : Int) :=
  True

-- Postcondition: result is true iff a and b have opposite signs
-- Using Int.sign: opposite signs means sign(a) * sign(b) = -1
def postcondition (a : Int) (b : Int) (result : Bool) :=
  result = true ↔ (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)

end Specs

section Impl

method hasOppositeSign (a : Int) (b : Int)
  return (result : Bool)
  require precondition a b
  ensures postcondition a b result
  do
  pure false

end Impl

section TestCases

-- Test case 1: negative and positive (from problem examples)
def test1_a : Int := -5
def test1_b : Int := 10
def test1_Expected : Bool := true

-- Test case 2: positive and negative
def test2_a : Int := 5
def test2_b : Int := -10
def test2_Expected : Bool := true

-- Test case 3: both positive
def test3_a : Int := 5
def test3_b : Int := 10
def test3_Expected : Bool := false

-- Test case 4: both negative
def test4_a : Int := -5
def test4_b : Int := -10
def test4_Expected : Bool := false

-- Test case 5: zero and positive
def test5_a : Int := 0
def test5_b : Int := 10
def test5_Expected : Bool := false

-- Test case 6: positive and zero
def test6_a : Int := 10
def test6_b : Int := 0
def test6_Expected : Bool := false

-- Test case 7: zero and negative
def test7_a : Int := 0
def test7_b : Int := -10
def test7_Expected : Bool := false

-- Test case 8: both zero
def test8_a : Int := 0
def test8_b : Int := 0
def test8_Expected : Bool := false

-- Test case 9: smallest opposite signs (-1 and 1)
def test9_a : Int := -1
def test9_b : Int := 1
def test9_Expected : Bool := true

-- Test case 10: smallest opposite signs (1 and -1)
def test10_a : Int := 1
def test10_b : Int := -1
def test10_Expected : Bool := true

-- Recommend to validate: 1, 3, 5

end TestCases
