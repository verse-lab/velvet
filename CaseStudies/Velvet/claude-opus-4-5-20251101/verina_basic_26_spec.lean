import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isEven: Determine whether a given integer is even
    Natural language breakdown:
    1. We have an input integer n
    2. An integer is even if it is divisible by 2 (i.e., n % 2 = 0)
    3. An integer is odd if it is not divisible by 2 (i.e., n % 2 ≠ 0)
    4. The function should return true if n is even, false otherwise
    5. There are no preconditions - any integer input is valid
    6. Zero is considered even (0 % 2 = 0)
    7. Negative even numbers are still even (e.g., -2 % 2 = 0)
    8. Negative odd numbers are still odd (e.g., -3 % 2 ≠ 0)

    Property-oriented specification:
    - If result is true: n is divisible by 2 (Even n holds)
    - If result is false: n is not divisible by 2 (Odd n holds)
    - We use the Mathlib definition of Even which states: Even n ↔ ∃ k, n = 2 * k
-/

section Specs

-- No custom helpers needed - we use Mathlib's Even predicate

-- Postcondition: result is true iff n is even
def ensures1 (n : Int) (result : Bool) :=
  result = true ↔ Even n

def precondition (n : Int) :=
  True  -- no preconditions; method works for any integer

def postcondition (n : Int) (result : Bool) :=
  ensures1 n result

end Specs

section Impl

method isEven (n : Int)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: Positive even number (from provided tests)
def test1_n : Int := 4
def test1_Expected : Bool := true

-- Test case 2: Positive odd number (from provided tests)
def test2_n : Int := 7
def test2_Expected : Bool := false

-- Test case 3: Zero is even (from provided tests)
def test3_n : Int := 0
def test3_Expected : Bool := true

-- Test case 4: Negative even number (from provided tests)
def test4_n : Int := -2
def test4_Expected : Bool := true

-- Test case 5: Negative odd number (from provided tests)
def test5_n : Int := -3
def test5_Expected : Bool := false

-- Test case 6: Large positive even number
def test6_n : Int := 1000
def test6_Expected : Bool := true

-- Test case 7: Large positive odd number
def test7_n : Int := 999
def test7_Expected : Bool := false

-- Test case 8: Small positive odd number (1)
def test8_n : Int := 1
def test8_Expected : Bool := false

-- Test case 9: Small positive even number (2)
def test9_n : Int := 2
def test9_Expected : Bool := true

-- Test case 10: Large negative even number
def test10_n : Int := -100
def test10_Expected : Bool := true

-- Recommend to validate: 1, 3, 5

end TestCases
