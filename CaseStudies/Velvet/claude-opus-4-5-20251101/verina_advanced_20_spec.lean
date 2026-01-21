import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isItEight: Return true if the input n is divisible by 8 or has 8 as one of its digits
    Natural language breakdown:
    1. We have an integer input n (can be positive, negative, or zero)
    2. The function should return true if n is divisible by 8 (n mod 8 = 0)
    3. The function should also return true if the digit 8 appears anywhere in the decimal representation of n
    4. For negative numbers, we consider the absolute value when checking for digit 8
    5. The two conditions are connected by OR - either condition being true makes the result true
    6. Zero is divisible by 8, so it returns true
    7. Examples:
       - 8: divisible by 8 AND contains digit 8 → true
       - 98: not divisible by 8, but contains digit 8 → true
       - 1224: divisible by 8 (1224 = 153 × 8), no digit 8 → true
       - 73: not divisible by 8, no digit 8 → false
       - -123456780: contains digit 8 → true
-/

section Specs

-- Mathematical definition: a natural number has digit 8 if there exists some
-- position k such that the k-th digit (from the right, 0-indexed) equals 8
def hasDigit8 (n : Nat) : Prop :=
  ∃ k : Nat, (n / (10^k)) % 10 = 8

-- Postcondition: result is true iff n is divisible by 8 or contains digit 8
def ensures1 (n : Int) (result : Bool) :=
  result = true ↔ (n % 8 = 0 ∨ hasDigit8 (Int.natAbs n))

def precondition (n : Int) :=
  True  -- no preconditions

def postcondition (n : Int) (result : Bool) :=
  ensures1 n result

end Specs

section Impl

method isItEight (n : Int)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: n = 8 (both divisible by 8 and contains 8)
def test1_n : Int := 8
def test1_Expected : Bool := true

-- Test case 2: n = 98 (not divisible by 8, but contains 8)
def test2_n : Int := 98
def test2_Expected : Bool := true

-- Test case 3: n = 1224 (divisible by 8, no digit 8)
def test3_n : Int := 1224
def test3_Expected : Bool := true

-- Test case 4: n = 73 (neither divisible by 8 nor contains 8)
def test4_n : Int := 73
def test4_Expected : Bool := false

-- Test case 5: n = 208 (divisible by 8 and contains 8)
def test5_n : Int := 208
def test5_Expected : Bool := true

-- Test case 6: n = 0 (divisible by 8)
def test6_n : Int := 0
def test6_Expected : Bool := true

-- Test case 7: n = -123456780 (negative, contains 8)
def test7_n : Int := -123456780
def test7_Expected : Bool := true

-- Test case 8: n = 1 (neither condition)
def test8_n : Int := 1
def test8_Expected : Bool := false

-- Test case 9: n = -9999 (negative, neither condition)
def test9_n : Int := -9999
def test9_Expected : Bool := false

-- Test case 10: n = -123453 (negative, neither condition)
def test10_n : Int := -123453
def test10_Expected : Bool := false

-- Recommend to validate: 1, 3, 4

end TestCases
