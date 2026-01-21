import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    lastDigit: extract the last decimal digit of a non-negative integer.
    Natural language breakdown:
    1. Input n is a natural number (hence non-negative by type).
    2. The last digit in base 10 is the remainder when dividing n by 10.
    3. The result must be a natural number between 0 and 9 inclusive.
    4. The returned digit must satisfy: result = n % 10.
-/

section Specs

-- Preconditions: no additional requirements because n : Nat is already non-negative.
def precondition (n : Nat) : Prop :=
  True

-- Postconditions:
-- 1) result is exactly the remainder mod 10
-- 2) result is a decimal digit (0..9), captured by result < 10
-- Note: the bound is redundant given result = n % 10, but kept for readability.
def postcondition (n : Nat) (result : Nat) : Prop :=
  result = n % 10 ∧ result < 10

end Specs

section Impl

method lastDigit (n : Nat) return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
    pure 0

end Impl

section TestCases

-- Test case 1: example from prompt
-- n = 123 -> 3

def test1_n : Nat := 123
def test1_Expected : Nat := 3

-- Test case 2: n = 0 -> 0

def test2_n : Nat := 0
def test2_Expected : Nat := 0

-- Test case 3: large number
-- 987654321 % 10 = 1

def test3_n : Nat := 987654321
def test3_Expected : Nat := 1

-- Test case 4: exact multiple of 10

def test4_n : Nat := 10
def test4_Expected : Nat := 0

-- Test case 5: repeated 9s

def test5_n : Nat := 999
def test5_Expected : Nat := 9

-- Test case 6: typical two-digit number

def test6_n : Nat := 45
def test6_Expected : Nat := 5

-- Test case 7: another multiple of 10

def test7_n : Nat := 100
def test7_Expected : Nat := 0

-- Test case 8: single digit remains unchanged

def test8_n : Nat := 5
def test8_Expected : Nat := 5

-- Recommend to validate: test1, test2, test4

end TestCases
