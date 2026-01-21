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
    CalSum: determine the sum of the first N natural numbers.
    Natural language breakdown:
    1. The input N is a natural number (Nat).
    2. The intended output is the sum 1 + 2 + ... + N.
    3. If N = 0, the sum is 0.
    4. For any N, the sum is characterized by the closed form N * (N + 1) / 2.
    5. There are no additional preconditions beyond providing a Nat.
-/

section Specs

-- Helper function: Gauss closed form for the sum 1 + 2 + ... + N.
-- We choose a fresh name to avoid collisions with any existing declarations.
-- Note: In Nat, division is truncated, but for N*(N+1) it is exact since the product is even.
def gaussSumCal (N : Nat) : Nat :=
  N * (N + 1) / 2

def precondition (N : Nat) : Prop :=
  True

def postcondition (N : Nat) (result : Nat) : Prop :=
  result = gaussSumCal N

end Specs

section Impl

method CalSum (N: Nat)
  return (result: Nat)
  require precondition N
  ensures postcondition N result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: example from prompt tests (N = 0)
-- Expected: 0

def test1_N : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: N = 1
-- Expected: 1

def test2_N : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: N = 5
-- Expected: 15

def test3_N : Nat := 5
def test3_Expected : Nat := 15

-- Test case 4: N = 10
-- Expected: 55

def test4_N : Nat := 10
def test4_Expected : Nat := 55

-- Test case 5: N = 20
-- Expected: 210

def test5_N : Nat := 20
def test5_Expected : Nat := 210

-- Additional representative cases

-- Test case 6: small even N = 2
-- Expected: 3

def test6_N : Nat := 2
def test6_Expected : Nat := 3

-- Test case 7: small odd N = 3
-- Expected: 6

def test7_N : Nat := 3
def test7_Expected : Nat := 6

-- Test case 8: larger but reasonable N = 100
-- Expected: 5050

def test8_N : Nat := 100
def test8_Expected : Nat := 5050

-- Recommend to validate: test1, test3, test4

end TestCases
