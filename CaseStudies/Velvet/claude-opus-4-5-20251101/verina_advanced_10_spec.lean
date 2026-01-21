import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Defs

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- findExponents: Decompose a natural number n into its prime factorization components
-- Natural language breakdown:
-- 1. Given a positive natural number n and a non-empty list of distinct primes
-- 2. n can be expressed as a product of powers of the given primes: n = ∏ p^e
-- 3. We need to find the exponent e for each prime p in the input list
-- 4. The output is a list of pairs (p, e) where p is a prime from the input and e is its exponent
-- 5. Every prime in the input list must appear in the output
-- 6. The primes in output should correspond to the input primes in order
-- 7. The exponent of a prime p in n is the p-adic valuation (how many times p divides n)
-- 8. Preconditions:
--    - n > 0 (positive number)
--    - primes is non-empty
--    - all elements in primes are prime numbers
--    - primes list has no duplicates
--    - n must be fully factorizable by the given primes (all prime factors of n are in the list)

section Specs

-- Helper: check if all elements in a list are prime
def allPrimes (primes : List Nat) : Prop :=
  ∀ p, p ∈ primes → Nat.Prime p

-- Helper: extract the first components of pairs
def firsts (pairs : List (Nat × Nat)) : List Nat :=
  pairs.map (fun ⟨p, _⟩ => p)

-- Helper: check if all prime factors of n are in the given list
def allPrimeFactorsIn (n : Nat) (primes : List Nat) : Prop :=
  ∀ p, Nat.Prime p → p ∣ n → p ∈ primes

-- Precondition: n is positive, primes is non-empty, all are prime, distinct, and n is fully factorizable
def precondition (n : Nat) (primes : List Nat) : Prop :=
  n > 0 ∧
  primes.length > 0 ∧
  allPrimes primes ∧
  primes.Nodup ∧
  allPrimeFactorsIn n primes

-- Postcondition:
-- 1. The result has the same length as the input primes list
-- 2. The primes in the result match the input primes in order
-- 3. For each pair (p, e) in result, e is the p-adic valuation of n
def postcondition (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) : Prop :=
  result.length = primes.length ∧
  firsts result = primes ∧
  (∀ i : Nat, i < result.length → (result[i]!.2 = Nat.factorization n (result[i]!.1)))

end Specs

section Impl

method findExponents (n : Nat) (primes : List Nat)
  return (result : List (Nat × Nat))
  require precondition n primes
  ensures postcondition n primes result
  do
  pure []

end Impl

section TestCases

-- Test case 1: n = 6 with primes [2, 3] (example from problem)
def test1_n : Nat := 6
def test1_primes : List Nat := [2, 3]
def test1_Expected : List (Nat × Nat) := [(2, 1), (3, 1)]

-- Test case 2: Large number with primes [2, 3, 5]
def test2_n : Nat := 6285195213566005335561053533150026217291776
def test2_primes : List Nat := [2, 3, 5]
def test2_Expected : List (Nat × Nat) := [(2, 55), (3, 55), (5, 0)]

-- Test case 3: n = 360 with primes [2, 3, 5]
def test3_n : Nat := 360
def test3_primes : List Nat := [2, 3, 5]
def test3_Expected : List (Nat × Nat) := [(2, 3), (3, 2), (5, 1)]

-- Test case 4: n = 18903812908 with primes [2, 43, 823, 133543]
def test4_n : Nat := 18903812908
def test4_primes : List Nat := [2, 43, 823, 133543]
def test4_Expected : List (Nat × Nat) := [(2, 2), (43, 1), (823, 1), (133543, 1)]

-- Test case 5: n = 114514 with primes [2, 31, 1847]
def test5_n : Nat := 114514
def test5_primes : List Nat := [2, 31, 1847]
def test5_Expected : List (Nat × Nat) := [(2, 1), (31, 1), (1847, 1)]

-- Test case 6: n = 20241147794175 with primes [3, 5, 7, 11, 31, 47]
def test6_n : Nat := 20241147794175
def test6_primes : List Nat := [3, 5, 7, 11, 31, 47]
def test6_Expected : List (Nat × Nat) := [(3, 3), (5, 2), (7, 1), (11, 3), (31, 1), (47, 3)]

-- Test case 7: Power of a single prime n = 32 = 2^5
def test7_n : Nat := 32
def test7_primes : List Nat := [2]
def test7_Expected : List (Nat × Nat) := [(2, 5)]

-- Test case 8: n = 1 (edge case - no prime divides 1, all exponents are 0)
def test8_n : Nat := 1
def test8_primes : List Nat := [2, 3]
def test8_Expected : List (Nat × Nat) := [(2, 0), (3, 0)]

-- Recommend to validate: 1, 3, 8

end TestCases
