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
    isPrime: Determine whether a given natural number is prime.
    Natural language breakdown:
    1. The input is a natural number n, and the task assumes n ≥ 2.
    2. A natural number n is prime iff it has no divisor k with 1 < k < n.
    3. Equivalently: n is prime iff for every k with 1 < k < n, k does not divide n.
    4. The method returns a Bool: true exactly when n is prime, and false otherwise.
    5. Inputs that violate n ≥ 2 are outside the intended domain.
-/

section Specs

-- Helper predicate: "n has a nontrivial divisor"
-- This matches the problem statement directly and avoids relying on any particular algorithm.
def HasNontrivialDivisor (n : Nat) : Prop :=
  ∃ k : Nat, 1 < k ∧ k < n ∧ k ∣ n

-- Precondition: input is expected to satisfy n ≥ 2.
def precondition (n : Nat) : Prop :=
  2 ≤ n

-- Postcondition: result is true iff there is no nontrivial divisor.
-- This uniquely determines the Bool output.
def postcondition (n : Nat) (result : Bool) : Prop :=
  result = true ↔ ¬ HasNontrivialDivisor n

end Specs

section Impl

method isPrime (n : Nat) return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  pure true

end Impl

section TestCases

-- Test case 1: n = 2 (smallest prime; example from prompt)
def test1_n : Nat := 2
def test1_Expected : Bool := true

-- Test case 2: n = 3 (prime)
def test2_n : Nat := 3
def test2_Expected : Bool := true

-- Test case 3: n = 4 (composite)
def test3_n : Nat := 4
def test3_Expected : Bool := false

-- Test case 4: n = 5 (prime)
def test4_n : Nat := 5
def test4_Expected : Bool := true

-- Test case 5: n = 9 (composite square)
def test5_n : Nat := 9
def test5_Expected : Bool := false

-- Test case 6: n = 11 (prime)
def test6_n : Nat := 11
def test6_Expected : Bool := true

-- Test case 7: n = 12 (composite even)
def test7_n : Nat := 12
def test7_Expected : Bool := false

-- Test case 8: n = 13 (prime)
def test8_n : Nat := 13
def test8_Expected : Bool := true

-- Reject input example (outside precondition): n = 0
-- This is not a test with expected output because it violates precondition.
def reject1_n : Nat := 0

-- Recommend to validate: 1, 3, 5

end TestCases
