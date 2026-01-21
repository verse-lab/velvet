import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    nthUglyNumber: Return the nth ugly number (1-indexed)
    
    Natural language breakdown:
    1. Ugly numbers are positive integers whose only prime factors are 2, 3, or 5
    2. The number 1 is considered ugly (it has no prime factors, vacuously satisfying the condition)
    3. Ugly numbers form an infinite sequence: 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, ...
    4. Given n (1-indexed), return the nth smallest ugly number
    5. A number m > 0 is ugly if and only if for every prime p that divides m, p ∈ {2, 3, 5}
    
    Key properties:
    - The input n must be at least 1 (1-indexed)
    - The result is always positive
    - The result is an ugly number
    - There are exactly n-1 ugly numbers smaller than the result
-/

section Specs

-- Property-based definition of ugly number (no recursion needed)
-- A number m is ugly iff m > 0 and every prime factor of m is 2, 3, or 5
def isUgly (m : Nat) : Prop :=
  m > 0 ∧ ∀ p : Nat, Nat.Prime p → p ∣ m → p = 2 ∨ p = 3 ∨ p = 5

-- Precondition: n must be at least 1 (1-indexed)
def require1 (n : Nat) := n ≥ 1

-- Postcondition clause 1: the result is positive and only has prime factors 2, 3, 5
def ensures1 (n : Nat) (result : Nat) := isUgly result

-- Postcondition clause 2: there are exactly n-1 ugly numbers strictly less than result
-- This ensures result is the nth smallest ugly number
def ensures2 (n : Nat) (result : Nat) := 
  Nat.card { x : Nat | isUgly x ∧ x < result } = n - 1

def precondition (n : Nat) := require1 n

def postcondition (n : Nat) (result : Nat) :=
  ensures1 n result ∧ ensures2 n result

end Specs

section Impl

method nthUglyNumber (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 1  -- placeholder

end Impl

section TestCases

-- Test case 1: n = 1, the first ugly number is 1
def test1_n : Nat := 1
def test1_Expected : Nat := 1

-- Test case 2: n = 10, the 10th ugly number is 12
def test2_n : Nat := 10
def test2_Expected : Nat := 12

-- Test case 3: n = 15, the 15th ugly number is 24
def test3_n : Nat := 15
def test3_Expected : Nat := 24

-- Test case 4: n = 5, the 5th ugly number is 5
def test4_n : Nat := 5
def test4_Expected : Nat := 5

-- Test case 5: n = 7, the 7th ugly number is 8
def test5_n : Nat := 7
def test5_Expected : Nat := 8

-- Test case 6: n = 2, the 2nd ugly number is 2
def test6_n : Nat := 2
def test6_Expected : Nat := 2

-- Test case 7: n = 3, the 3rd ugly number is 3
def test7_n : Nat := 3
def test7_Expected : Nat := 3

-- Test case 8: n = 4, the 4th ugly number is 4
def test8_n : Nat := 4
def test8_Expected : Nat := 4

-- Test case 9: n = 6, the 6th ugly number is 6
def test9_n : Nat := 6
def test9_Expected : Nat := 6

-- Test case 10: n = 11, the 11th ugly number is 15
def test10_n : Nat := 11
def test10_Expected : Nat := 15

-- Recommend to validate: 1, 2, 4

end TestCases
