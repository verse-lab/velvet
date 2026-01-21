import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isDivisibleBy11: Determine whether a given integer is divisible by 11
    Natural language breakdown:
    1. We have an input integer n
    2. An integer n is divisible by 11 if and only if n mod 11 equals 0
    3. The function should return true if n is divisible by 11
    4. The function should return false if n is not divisible by 11
    5. Zero is divisible by 11 (0 mod 11 = 0)
    6. Negative numbers follow the same rule: -11 mod 11 = 0, so -11 is divisible by 11
    7. The modulo operation for Int in Lean uses Euclidean modulo (Int.emod)

    Property-oriented specification:
    - result = true iff n % 11 = 0
    - result = false iff n % 11 ≠ 0
    - This is a simple decidable predicate on integers
-/

section Specs

-- Precondition: no restrictions on input
def precondition (n : Int) :=
  True

-- Postcondition: result is true iff n is divisible by 11
def postcondition (n : Int) (result : Bool) :=
  result = true ↔ n % 11 = 0

end Specs

section Impl

method isDivisibleBy11 (n: Int)
  return (result: Bool)
  require precondition n
  ensures postcondition n result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: Zero is divisible by 11
def test1_n : Int := 0
def test1_Expected : Bool := true

-- Test case 2: 11 is divisible by 11
def test2_n : Int := 11
def test2_Expected : Bool := true

-- Test case 3: 22 is divisible by 11
def test3_n : Int := 22
def test3_Expected : Bool := true

-- Test case 4: 23 is not divisible by 11
def test4_n : Int := 23
def test4_Expected : Bool := false

-- Test case 5: 33 is divisible by 11
def test5_n : Int := 33
def test5_Expected : Bool := true

-- Test case 6: -11 (negative) is divisible by 11
def test6_n : Int := -11
def test6_Expected : Bool := true

-- Test case 7: -22 (negative) is divisible by 11
def test7_n : Int := -22
def test7_Expected : Bool := true

-- Test case 8: 1 is not divisible by 11
def test8_n : Int := 1
def test8_Expected : Bool := false

-- Test case 9: -1 (negative) is not divisible by 11
def test9_n : Int := -1
def test9_Expected : Bool := false

-- Test case 10: 121 (11*11) is divisible by 11
def test10_n : Int := 121
def test10_Expected : Bool := true

-- Recommend to validate: 1, 2, 6

end TestCases

