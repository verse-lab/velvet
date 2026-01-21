import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isArmstrong: Determine whether a given number n is an Armstrong number
    Natural language breakdown:
    1. An Armstrong number (also called Narcissistic number) is a number that equals
       the sum of its own digits each raised to the power of the number of digits
    2. The number of digits k of n in base 10 is: if n = 0 then 1 else floor(log10(n)) + 1
    3. The digit at position i (0-indexed from right) is: (n / 10^i) % 10
    4. The Armstrong sum is: sum of (digit at position i)^k for i from 0 to k-1
    5. n is an Armstrong number iff the Armstrong sum equals n
    6. Examples:
       - 153 has 3 digits: 1^3 + 5^3 + 3^3 = 1 + 125 + 27 = 153 ✓
       - 9474 has 4 digits: 9^4 + 4^4 + 7^4 + 4^4 = 6561 + 256 + 2401 + 256 = 9474 ✓
       - 10 has 2 digits: 1^2 + 0^2 = 1 + 0 = 1 ≠ 10 ✗
    7. Edge cases:
       - 0 is an Armstrong number (0 has 1 digit, 0^1 = 0)
       - Single digit numbers (1-9) are all Armstrong numbers (d^1 = d)
-/

section Specs

register_specdef_allow_recursion

-- Number of digits in base 10 (mathematically defined)
def numDigits (n : Nat) : Nat :=
  if n < 10 then 1 else 1 + numDigits (n / 10)

-- Get digit at position i (0-indexed from right)
def digitAt (n : Nat) (i : Nat) : Nat :=
  (n / (10 ^ i)) % 10

-- Armstrong sum: sum of (digit at position i)^k for i from 0 to k-1
def armstrongSumAux (n : Nat) (k : Nat) (i : Nat) : Nat :=
  if i = 0 then 0
  else armstrongSumAux n k (i - 1) + (digitAt n (i - 1)) ^ k

def armstrongSum (n : Nat) : Nat :=
  let k := numDigits n
  armstrongSumAux n k k

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Bool) : Prop :=
  result = true ↔ armstrongSum n = n

end Specs

section Impl

method isArmstrong (n : Nat)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
    pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: 0 is an Armstrong number (0^1 = 0)
def test1_n : Nat := 0
def test1_Expected : Bool := true

-- Test case 2: 1 is an Armstrong number (1^1 = 1)
def test2_n : Nat := 1
def test2_Expected : Bool := true

-- Test case 3: 10 is not an Armstrong number (1^2 + 0^2 = 1 ≠ 10)
def test3_n : Nat := 10
def test3_Expected : Bool := false

-- Test case 4: 153 is an Armstrong number (1^3 + 5^3 + 3^3 = 153)
def test4_n : Nat := 153
def test4_Expected : Bool := true

-- Test case 5: 9474 is an Armstrong number (9^4 + 4^4 + 7^4 + 4^4 = 9474)
def test5_n : Nat := 9474
def test5_Expected : Bool := true

-- Test case 6: 9475 is not an Armstrong number
def test6_n : Nat := 9475
def test6_Expected : Bool := false

-- Test case 7: 370 is an Armstrong number (3^3 + 7^3 + 0^3 = 27 + 343 + 0 = 370)
def test7_n : Nat := 370
def test7_Expected : Bool := true

-- Test case 8: 9 is an Armstrong number (single digit, 9^1 = 9)
def test8_n : Nat := 9
def test8_Expected : Bool := true

-- Test case 9: 100 is not an Armstrong number (1^3 + 0^3 + 0^3 = 1 ≠ 100)
def test9_n : Nat := 100
def test9_Expected : Bool := false

-- Recommend to validate: 3, 4, 5 (covers false case 10, classic 3-digit Armstrong 153, and 4-digit 9474)

end TestCases
