import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isDivisibleBy11: Determine whether a given integer is divisible by 11
    Natural language breakdown:
    1. We have an input integer n
    2. An integer n is divisible by 11 if and only if there exists an integer k such that n = 11 * k
    3. Equivalently, n is divisible by 11 if and only if n % 11 = 0
    4. The method should return true if n is divisible by 11
    5. The method should return false if n is not divisible by 11
    6. Zero is divisible by 11 (0 = 11 * 0)
    7. Negative integers can also be divisible by 11 (e.g., -11, -22)
    8. The divisibility relation is symmetric under negation

    Property-oriented specification:
    - We use the built-in divisibility predicate from Lean: 11 ∣ n
    - This means: there exists an integer c such that n = 11 * c
    - The result should be true if and only if 11 divides n
-/

section Specs

-- Use Lean's built-in divisibility predicate for integers
-- 11 ∣ n means: ∃ c, n = 11 * c

def precondition (n : Int) :=
  True  -- no preconditions

def postcondition (n : Int) (result : Bool) :=
  result = true ↔ (11 : Int) ∣ n

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

-- Test case 6: -11 is divisible by 11
def test6_n : Int := -11
def test6_Expected : Bool := true

-- Test case 7: -22 is divisible by 11
def test7_n : Int := -22
def test7_Expected : Bool := true

-- Test case 8: 1 is not divisible by 11
def test8_n : Int := 1
def test8_Expected : Bool := false

-- Test case 9: -1 is not divisible by 11
def test9_n : Int := -1
def test9_Expected : Bool := false

-- Test case 10: 121 is divisible by 11 (11 * 11)
def test10_n : Int := 121
def test10_Expected : Bool := true

-- Recommend to validate: 1, 2, 4

end TestCases
