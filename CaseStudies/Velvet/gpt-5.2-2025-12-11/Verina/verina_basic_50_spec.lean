import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    Abs: compute the absolute value of an integer.
    Natural language breakdown:
    1. The input is an integer x.
    2. The output is a non-negative integer value representing the magnitude of x.
    3. If x is non-negative (0 ≤ x), the output equals x.
    4. If x is negative (x < 0), the output equals -x.
    5. The output is always non-negative.
    6. The function must handle x = 0, x > 0, and x < 0.
-/

section Specs

-- Helper observation: we use Mathlib's absolute value on Int, written `Int.natAbs` or `Int.abs`.
-- For this task, we stay in Int as return type, so we describe the result via order + equations.

-- A simple, fully characterizing specification of absolute value on Int.
-- It uniquely determines result because it pins down exactly which of the two values (x or -x)
-- must be returned depending on the sign of x, and also requires non-negativity.

def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  ((x ≥ 0 ∧ result = x) ∨ (x < 0 ∧ result = -x))

end Specs

section Impl

method Abs (x: Int) return (result: Int)
  require precondition x
  ensures postcondition x result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: example from prompt: x = 5
def test1_x : Int := 5
def test1_Expected : Int := 5

-- Test case 2: x = 0
def test2_x : Int := 0
def test2_Expected : Int := 0

-- Test case 3: x = -5
def test3_x : Int := -5
def test3_Expected : Int := 5

-- Test case 4: x = 10
def test4_x : Int := 10
def test4_Expected : Int := 10

-- Test case 5: x = -10
def test5_x : Int := -10
def test5_Expected : Int := 10

-- Additional coverage: smallest magnitudes around zero
-- Test case 6: x = 1
def test6_x : Int := 1
def test6_Expected : Int := 1

-- Test case 7: x = -1
def test7_x : Int := -1
def test7_Expected : Int := 1

-- Larger magnitude
-- Test case 8: x = 123456
def test8_x : Int := 123456
def test8_Expected : Int := 123456

-- Larger negative magnitude
-- Test case 9: x = -123456
def test9_x : Int := -123456
def test9_Expected : Int := 123456

-- Recommend to validate: 1, 2, 3

end TestCases
