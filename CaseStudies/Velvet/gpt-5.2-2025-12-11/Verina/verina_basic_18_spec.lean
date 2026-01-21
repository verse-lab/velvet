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
    sumOfDigits: compute the sum of the base-10 digits of a non-negative integer.
    Natural language breakdown:
    1. The input n is a natural number (a non-negative integer).
    2. Consider the canonical base-10 digit list of n given by Mathlib: `Nat.digits 10 n`.
       This list is in little-endian order (least-significant digit first).
    3. Each element of `Nat.digits 10 n` is a digit in the range 0..9.
    4. The output is the sum of these digits.
    5. In particular, for n = 0, the digit list is empty and the sum is 0.
    6. The result is a natural number.
-/

section Specs

-- No special precondition: input is already a Nat.
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: result is exactly the sum of the canonical base-10 digits.
-- Using `Nat.digits` makes the specification canonical and uniquely determines the result.
def postcondition (n : Nat) (result : Nat) : Prop :=
  result = (Nat.digits 10 n).sum

end Specs

section Impl

method sumOfDigits (n : Nat) return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: example from prompt
-- 12345 -> 1+2+3+4+5 = 15

def test1_n : Nat := 12345
def test1_Expected : Nat := 15

-- Test case 2: zero

def test2_n : Nat := 0
def test2_Expected : Nat := 0

-- Test case 3: large mixed digits

def test3_n : Nat := 987654321
def test3_Expected : Nat := 45

-- Test case 4: repeated ones

def test4_n : Nat := 11111
def test4_Expected : Nat := 5

-- Test case 5: includes zeros in the middle

def test5_n : Nat := 1001
def test5_Expected : Nat := 2

-- Test case 6: all 9s

def test6_n : Nat := 9999
def test6_Expected : Nat := 36

-- Test case 7: single digit

def test7_n : Nat := 7
def test7_Expected : Nat := 7

-- Test case 8: trailing zeros

def test8_n : Nat := 1200
def test8_Expected : Nat := 3

-- Test case 9: power of 10

def test9_n : Nat := 10000
def test9_Expected : Nat := 1

-- Recommend to validate: test1, test2, test5

end TestCases
