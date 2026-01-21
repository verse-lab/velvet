import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    minOfThree: Find the minimum among three given integers
    
    Natural language breakdown:
    1. We are given three integers a, b, and c
    2. We need to return the smallest value among these three
    3. The result must be less than or equal to each of the input numbers
    4. The result must be equal to one of the input values (a, b, or c)
    5. No preconditions needed - works for any three integers
    6. The result is uniquely determined by these constraints
-/

section Specs

-- Precondition: No constraints needed for three integers
def precondition (a : Int) (b : Int) (c : Int) : Prop :=
  True

-- Postcondition clauses:
-- 1. Result is less than or equal to each input
def ensures1 (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  result ≤ a ∧ result ≤ b ∧ result ≤ c

-- 2. Result is one of the three input values
def ensures2 (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  result = a ∨ result = b ∨ result = c

def postcondition (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  ensures1 a b c result ∧ ensures2 a b c result

end Specs

section Impl

method minOfThree (a : Int) (b : Int) (c : Int)
  return (result : Int)
  require precondition a b c
  ensures postcondition a b c result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Decreasing order (from problem examples)
def test1_a : Int := 3
def test1_b : Int := 2
def test1_c : Int := 1
def test1_Expected : Int := 1

-- Test case 2: All equal values
def test2_a : Int := 5
def test2_b : Int := 5
def test2_c : Int := 5
def test2_Expected : Int := 5

-- Test case 3: First element is minimum
def test3_a : Int := 10
def test3_b : Int := 20
def test3_c : Int := 15
def test3_Expected : Int := 10

-- Test case 4: First element is negative minimum
def test4_a : Int := -1
def test4_b : Int := 2
def test4_c : Int := 3
def test4_Expected : Int := -1

-- Test case 5: Second element is negative minimum
def test5_a : Int := 2
def test5_b : Int := -3
def test5_c : Int := 4
def test5_Expected : Int := -3

-- Test case 6: Third element is negative minimum
def test6_a : Int := 2
def test6_b : Int := 3
def test6_c : Int := -5
def test6_Expected : Int := -5

-- Test case 7: Two zeros and a positive
def test7_a : Int := 0
def test7_b : Int := 0
def test7_c : Int := 1
def test7_Expected : Int := 0

-- Test case 8: Mixed with zero
def test8_a : Int := 0
def test8_b : Int := -1
def test8_c : Int := 1
def test8_Expected : Int := -1

-- Test case 9: All negative values
def test9_a : Int := -5
def test9_b : Int := -2
def test9_c : Int := -3
def test9_Expected : Int := -5

-- Recommend to validate: 1, 4, 9

end TestCases
