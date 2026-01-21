import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isPerfectSquare: Determine whether a given natural number is a perfect square
    Natural language breakdown:
    1. We have an input natural number n (non-negative)
    2. A perfect square is a number that equals k * k for some natural number k
    3. Return true if there exists a natural number k such that k * k = n
    4. Return false if no such natural number k exists
    5. 0 is a perfect square (0 = 0 * 0)
    6. 1 is a perfect square (1 = 1 * 1)
    7. Using Mathlib: Nat.exists_mul_self states (∃ n, n * n = x) ↔ sqrt x * sqrt x = x
    8. This means we can characterize perfect squares using the integer square root
-/

section Specs

-- Helper Functions

-- A number is a perfect square if there exists k such that k * k = n
-- Using Mathlib's characterization: n is a perfect square iff sqrt(n) * sqrt(n) = n
def isPerfectSquareProp (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n

-- Postcondition clauses
def ensures1 (n : Nat) (result : Bool) :=
  result = true ↔ isPerfectSquareProp n

def precondition (n : Nat) :=
  True  -- no preconditions, all natural numbers are valid inputs

def postcondition (n : Nat) (result : Bool) :=
  ensures1 n result

end Specs

section Impl

-- Method Definition

method isPerfectSquare (n : Nat)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: 0 is a perfect square (0 = 0 * 0)
def test1_n : Nat := 0
def test1_Expected : Bool := true

-- Test case 2: 1 is a perfect square (1 = 1 * 1)
def test2_n : Nat := 1
def test2_Expected : Bool := true

-- Test case 3: 4 is a perfect square (4 = 2 * 2)
def test3_n : Nat := 4
def test3_Expected : Bool := true

-- Test case 4: 9 is a perfect square (9 = 3 * 3)
def test4_n : Nat := 9
def test4_Expected : Bool := true

-- Test case 5: 2 is not a perfect square
def test5_n : Nat := 2
def test5_Expected : Bool := false

-- Test case 6: 3 is not a perfect square
def test6_n : Nat := 3
def test6_Expected : Bool := false

-- Test case 7: 10 is not a perfect square
def test7_n : Nat := 10
def test7_Expected : Bool := false

-- Test case 8: 16 is a perfect square (16 = 4 * 4)
def test8_n : Nat := 16
def test8_Expected : Bool := true

-- Test case 9: 25 is a perfect square (25 = 5 * 5)
def test9_n : Nat := 25
def test9_Expected : Bool := true

-- Test case 10: 26 is not a perfect square
def test10_n : Nat := 26
def test10_Expected : Bool := false

-- Recommend to validate: 1, 3, 5

end TestCases
