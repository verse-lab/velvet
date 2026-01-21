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
    isPerfectSquare: determine whether a natural number is a perfect square
    Natural language breakdown:
    1. The input n is a natural number (so it is non-negative).
    2. The output is a Boolean value.
    3. The output should be true exactly when there exists a natural number k such that k*k = n.
    4. The output should be false exactly when there is no natural number k such that k*k = n.
    5. Edge cases: 0 and 1 are perfect squares.
    6. Examples: 4, 9, 16, 25 are perfect squares; 2, 3, 10, 26 are not.
-/

section Specs

-- A natural number n is a perfect square iff it is the square of some natural number.
-- We use k*k rather than k^2 to keep the predicate simple.
def IsSquareNat (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n

-- No preconditions.
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: the boolean result reflects existence of a square root in Nat.
-- Two clauses together uniquely determine the Bool result.
def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ IsSquareNat n) ∧
  (result = false ↔ ¬ IsSquareNat n)

end Specs

section Impl

method isPerfectSquare (n : Nat) return (result : Bool)
  require precondition (n)
  ensures postcondition (n) (result)
  do
    pure false  -- placeholder body

end Impl

section TestCases

-- Test case 1: example from prompt: n=0 is a perfect square (0*0)
def test1_n : Nat := 0
def test1_Expected : Bool := true

-- Test case 2: n=1 is a perfect square (1*1)
def test2_n : Nat := 1
def test2_Expected : Bool := true

-- Test case 3: n=4 is a perfect square (2*2)
def test3_n : Nat := 4
def test3_Expected : Bool := true

-- Test case 4: n=9 is a perfect square (3*3)
def test4_n : Nat := 9
def test4_Expected : Bool := true

-- Test case 5: n=2 is not a perfect square
def test5_n : Nat := 2
def test5_Expected : Bool := false

-- Test case 6: n=3 is not a perfect square
def test6_n : Nat := 3
def test6_Expected : Bool := false

-- Test case 7: n=10 is not a perfect square
def test7_n : Nat := 10
def test7_Expected : Bool := false

-- Test case 8: n=16 is a perfect square (4*4)
def test8_n : Nat := 16
def test8_Expected : Bool := true

-- Test case 9: n=25 is a perfect square (5*5)
def test9_n : Nat := 25
def test9_Expected : Bool := true

-- Test case 10: n=26 is not a perfect square
def test10_n : Nat := 26
def test10_Expected : Bool := false

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test5, test8

end TestCases
