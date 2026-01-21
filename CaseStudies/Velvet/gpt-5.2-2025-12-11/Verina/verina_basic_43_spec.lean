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
    sumOfFourthPowerOfOddNumbers: compute the sum of the fourth powers of the first n odd natural numbers.
    Natural language breakdown:
    1. The input n is a natural number representing how many odd numbers are included.
    2. The k-th odd natural number (0-based) is (2*k + 1).
    3. We consider the first n odd numbers: (2*0+1), (2*1+1), ..., (2*(n-1)+1).
    4. Each of these odd numbers is raised to the 4th power.
    5. The output is the sum of these fourth powers.
    6. If n = 0, the sum is over an empty collection and equals 0.
-/

section Specs

-- Helper: the k-th odd natural number (0-based)
def oddAt (k : Nat) : Nat := 2 * k + 1

-- Helper: sum of fourth powers of the first n odd numbers, as a finite sum over `range n`.
-- We avoid the binder notation `∑ k in ...` because it may not parse in this environment.
def sumFourthOdd (n : Nat) : Nat :=
  (Finset.range n).sum (fun k => (oddAt k) ^ 4)

-- No preconditions: n is a Nat already.
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: the result is exactly the finite sum of the fourth powers of the first n odd numbers.
def postcondition (n : Nat) (result : Nat) : Prop :=
  result = sumFourthOdd n

end Specs

section Impl

method sumOfFourthPowerOfOddNumbers (n: Nat) return (result: Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: example n = 0
-- Sum over empty set = 0

def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: n = 1 => 1^4 = 1

def test2_n : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: n = 2 => 1^4 + 3^4 = 1 + 81 = 82

def test3_n : Nat := 2
def test3_Expected : Nat := 82

-- Test case 4: n = 3 => 1^4 + 3^4 + 5^4 = 707

def test4_n : Nat := 3
def test4_Expected : Nat := 707

-- Test case 5: n = 4 => previous + 7^4 = 3108

def test5_n : Nat := 4
def test5_Expected : Nat := 3108

-- Test case 6: n = 5 => previous + 9^4 = 9669

def test6_n : Nat := 5
def test6_Expected : Nat := 9669

-- Test case 7: n = 6 => previous + 11^4 = 24310

def test7_n : Nat := 6
def test7_Expected : Nat := 24310

-- Test case 8: n = 7 => previous + 13^4 = 52871

def test8_n : Nat := 7
def test8_Expected : Nat := 52871

-- Test case 9: n = 8 => previous + 15^4 = 103496

def test9_n : Nat := 8
def test9_Expected : Nat := 103496

-- Recommend to validate: test1, test2, test6

end TestCases
