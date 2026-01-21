import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isPowerOfTwo: Determine whether a given integer is a power of two
    Natural language breakdown:
    1. We have an input integer n
    2. An integer n is a power of two if there exists a non-negative integer x such that n = 2^x
    3. The function should return true if n is a power of two, false otherwise
    4. Negative numbers are not powers of two (return false)
    5. Zero is not a power of two (return false)
    6. The value 1 is a power of two (2^0 = 1)
    7. Examples of powers of two: 1, 2, 4, 8, 16, 32, 64, ...
    8. Examples of non-powers of two: 0, 3, 5, 6, 7, 9, 10, ...

    Property-oriented specification:
    - If result is true: n is positive and there exists a natural number x such that n = 2^x
    - If result is false: either n <= 0 or there is no natural number x such that n = 2^x
    - This can be expressed as: result = true ↔ (n > 0 ∧ ∃ x : Nat, n = 2^x)
-/

section Specs

-- Helper Functions

-- Predicate: check if an integer is a power of two
-- n is a power of two if n > 0 and there exists a natural number x such that n = 2^x
def isPowerOfTwoProp (n : Int) : Prop :=
  n > 0 ∧ ∃ x : Nat, n = (2 : Int) ^ x

-- Postcondition clauses
def ensures1 (n : Int) (result : Bool) :=
  result = true ↔ isPowerOfTwoProp n

def precondition (n : Int) :=
  True  -- no preconditions

def postcondition (n : Int) (result : Bool) :=
  ensures1 n result

end Specs

section Impl

method isPowerOfTwo (n : Int)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  pure false  -- placeholder

end Impl

section TestCases

-- Test case 1: n = 1, which is 2^0 (power of two)
def test1_n : Int := 1
def test1_Expected : Bool := true

-- Test case 2: n = 16, which is 2^4 (power of two)
def test2_n : Int := 16
def test2_Expected : Bool := true

-- Test case 3: n = 3, not a power of two
def test3_n : Int := 3
def test3_Expected : Bool := false

-- Test case 4: n = 0, not a power of two (zero case)
def test4_n : Int := 0
def test4_Expected : Bool := false

-- Test case 5: n = -2, negative number (not a power of two)
def test5_n : Int := -2
def test5_Expected : Bool := false

-- Test case 6: n = 8, which is 2^3 (power of two)
def test6_n : Int := 8
def test6_Expected : Bool := true

-- Test case 7: n = 10, not a power of two
def test7_n : Int := 10
def test7_Expected : Bool := false

-- Test case 8: n = 2, which is 2^1 (power of two)
def test8_n : Int := 2
def test8_Expected : Bool := true

-- Test case 9: n = 64, which is 2^6 (power of two)
def test9_n : Int := 64
def test9_Expected : Bool := true

-- Test case 10: n = -16, negative power of two base (not a power of two)
def test10_n : Int := -16
def test10_Expected : Bool := false

-- Recommend to validate: 1, 2, 4

end TestCases
