import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    singleDigitPrimeFactor: Given a natural number n, returns the smallest prime factor that is less than 10. If none exist, return 0.
    
    Natural language breakdown:
    1. We need to find prime factors of n that are less than 10
    2. Single-digit primes are: 2, 3, 5, 7
    3. A prime factor of n is a prime number p such that p divides n
    4. We want the smallest such prime factor (minimum among qualifying factors)
    5. If no such prime factor exists, return 0
    6. For n = 0: By convention in the problem, return 0 (special case)
    7. For n = 1: 1 has no prime factors, return 0
    8. For primes >= 10: if n is a prime >= 10 or product of such primes, return 0
-/

section Specs

-- The set of single-digit primes
def singleDigitPrimes : List Nat := [2, 3, 5, 7]

-- Precondition: no restrictions on input
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: result is either 0 (no single-digit prime factor or n <= 1) or the smallest single-digit prime factor
def postcondition (n : Nat) (result : Nat) : Prop :=
  -- Case 1: result is 0 means n <= 1 or no single-digit prime divides n
  (result = 0 ↔ n ≤ 1 ∨ ∀ p ∈ singleDigitPrimes, ¬(p ∣ n)) ∧
  -- Case 2: if result is not 0, it must be a single-digit prime factor and the smallest one
  (result ≠ 0 → (result ∈ singleDigitPrimes ∧ result ∣ n ∧ 
    ∀ p ∈ singleDigitPrimes, p ∣ n → result ≤ p))

end Specs

section Impl

method singleDigitPrimeFactor (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: n = 0, special case returns 0
def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: n = 98 = 2 * 49 = 2 * 7^2, smallest single-digit prime factor is 2
def test2_n : Nat := 98
def test2_Expected : Nat := 2

-- Test case 3: n = 9 = 3^2, smallest single-digit prime factor is 3
def test3_n : Nat := 9
def test3_Expected : Nat := 3

-- Test case 4: n = 73 (prime >= 10), no single-digit prime factors
def test4_n : Nat := 73
def test4_Expected : Nat := 0

-- Test case 5: n = 529 = 23^2 (prime >= 10 squared), no single-digit prime factors
def test5_n : Nat := 529
def test5_Expected : Nat := 0

-- Test case 6: n = 161 = 7 * 23, smallest single-digit prime factor is 7
def test6_n : Nat := 161
def test6_Expected : Nat := 7

-- Test case 7: n = 1, no prime factors
def test7_n : Nat := 1
def test7_Expected : Nat := 0

-- Test case 8: n = 2, smallest prime, returns 2
def test8_n : Nat := 2
def test8_Expected : Nat := 2

-- Test case 9: n = 35 = 5 * 7, smallest single-digit prime factor is 5
def test9_n : Nat := 35
def test9_Expected : Nat := 5

-- Test case 10: n = 121 = 11^2, no single-digit prime factors
def test10_n : Nat := 121
def test10_Expected : Nat := 0

-- Recommend to validate: 1, 2, 6

end TestCases
