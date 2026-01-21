import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    countSumDivisibleBy: Count numbers smaller than n whose digit sum is divisible by d
    Natural language breakdown:
    1. Given a natural number n and a divisor d (where d > 0)
    2. For each number k in the range [0, n), compute the sum of its digits
    3. Check if this digit sum is divisible by d
    4. Count how many such numbers satisfy this divisibility condition
    5. The digit sum of a number is the sum of all its decimal digits
       - e.g., digitSum(123) = 1 + 2 + 3 = 6
    6. A number's digit sum is divisible by d if d ∣ digitSum(k)
    7. Edge cases:
       - n = 0: no numbers to check, result is 0
       - n = 1: only check 0, digitSum(0) = 0, d ∣ 0 always, so result is 1
       - d = 1: all digit sums are divisible by 1, result is n
-/

section Specs
register_specdef_allow_recursion

-- Helper function to compute the sum of digits of a natural number
-- This is a standard mathematical concept that requires recursion
def digitSum (n : Nat) : Nat :=
  if n < 10 then n
  else (n % 10) + digitSum (n / 10)

-- Precondition: d must be positive
def precondition (n : Nat) (d : Nat) : Prop :=
  d > 0

-- Postcondition: result equals the cardinality of the set of numbers in [0, n)
-- whose digit sum is divisible by d
-- Using Finset.filter and Finset.range for a property-based specification
def postcondition (n : Nat) (d : Nat) (result : Nat) : Prop :=
  result = (Finset.filter (fun k => d ∣ digitSum k) (Finset.range n)).card

end Specs

section Impl

method countSumDivisibleBy (n : Nat) (d : Nat)
  return (result : Nat)
  require precondition n d
  ensures postcondition n d result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: n = 0, d = 2 - no numbers to check
def test1_n : Nat := 0
def test1_d : Nat := 2
def test1_Expected : Nat := 0

-- Test case 2: n = 1, d = 2 - only 0, digitSum(0) = 0, divisible by 2
def test2_n : Nat := 1
def test2_d : Nat := 2
def test2_Expected : Nat := 1

-- Test case 3: n = 10, d = 3 - check 0-9, digitSums divisible by 3: 0, 3, 6, 9
def test3_n : Nat := 10
def test3_d : Nat := 3
def test3_Expected : Nat := 4

-- Test case 4: n = 12, d = 2 - check 0-11
-- digitSums: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2
-- divisible by 2: 0, 2, 4, 6, 8, 11 (positions with even digit sums) = 6
def test4_n : Nat := 12
def test4_d : Nat := 2
def test4_Expected : Nat := 6

-- Test case 5: n = 20, d = 5 - check 0-19
-- Numbers with digit sum divisible by 5: 0 (sum=0), 5 (sum=5), 14 (sum=5), 19 (sum=10)
def test5_n : Nat := 20
def test5_d : Nat := 5
def test5_Expected : Nat := 4

-- Test case 6: n = 5, d = 1 - all digit sums divisible by 1
def test6_n : Nat := 5
def test6_d : Nat := 1
def test6_Expected : Nat := 5

-- Test case 7: n = 100, d = 9 - checking larger range
-- Numbers 0-99 with digit sum divisible by 9: 0, 9, 18, 27, 36, 45, 54, 63, 72, 81, 90, 99 = 12
def test7_n : Nat := 100
def test7_d : Nat := 9
def test7_Expected : Nat := 12

-- Test case 8: n = 15, d = 7
-- digitSums: 0,1,2,3,4,5,6,7,8,9,1,2,3,4,5
-- divisible by 7: 0 (sum=0), 7 (sum=7) = 2
def test8_n : Nat := 15
def test8_d : Nat := 7
def test8_Expected : Nat := 2

-- Recommend to validate: 1, 2, 6

end TestCases
