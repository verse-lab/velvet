import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
--    ComputeAvg: Compute the average of two integers using integer division
--    Natural language breakdown:
--    1. Given two integers a and b, compute their average using integer division
--    2. The true arithmetic mean is (a + b) / 2, but integer division may truncate
--    3. The result must satisfy the floor division property:
--       result is the largest integer such that 2 * result ≤ a + b
--    4. This is equivalent to: 2 * result ≤ a + b < 2 * result + 2
--    5. This uniquely determines the result as floor((a + b) / 2)
--    6. For even sums: (a + b) / 2 is exact, so 2 * result = a + b
--    7. For odd sums: 2 * result = a + b - 1 (floor division truncates down)
--    8. The specification uses standard integer division (Int.ediv in Lean)
--    9. Examples:
--       - a=4, b=6: sum=10, avg=5, 2*5=10, 10 ≤ 10 < 12 ✓
--       - a=3, b=5: sum=8, avg=4, 2*4=8, 8 ≤ 8 < 10 ✓
--       - a=3, b=4: sum=7, avg=3, 2*3=6, 6 ≤ 7 < 8 ✓
--       - a=-3, b=7: sum=4, avg=2, 2*2=4, 4 ≤ 4 < 6 ✓
--       - a=-5, b=5: sum=0, avg=0, 2*0=0, 0 ≤ 0 < 2 ✓

section Specs

-- Precondition: no constraints needed, any two integers are valid inputs
def precondition (a : Int) (b : Int) : Prop :=
  True

-- Postcondition: the computed average is the floor of (a + b) / 2
-- This is uniquely determined by: 2 * result ≤ a + b < 2 * result + 2
def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  2 * result ≤ a + b ∧ a + b < 2 * result + 2

end Specs

section Impl

method ComputeAvg (a : Int) (b : Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Two positive even numbers with even sum
def test1_a : Int := 4
def test1_b : Int := 6
def test1_Expected : Int := 5

-- Test case 2: Two positive odd numbers with even sum
def test2_a : Int := 3
def test2_b : Int := 5
def test2_Expected : Int := 4

-- Test case 3: Two positive numbers with odd sum (truncation case)
def test3_a : Int := 3
def test3_b : Int := 4
def test3_Expected : Int := 3

-- Test case 4: Mixed signs with positive sum
def test4_a : Int := -3
def test4_b : Int := 7
def test4_Expected : Int := 2

-- Test case 5: Opposite numbers summing to zero
def test5_a : Int := -5
def test5_b : Int := 5
def test5_Expected : Int := 0

-- Test case 6: Two negative numbers
def test6_a : Int := -8
def test6_b : Int := -4
def test6_Expected : Int := -6

-- Test case 7: Both zero
def test7_a : Int := 0
def test7_b : Int := 0
def test7_Expected : Int := 0

-- Test case 8: One zero, one positive
def test8_a : Int := 0
def test8_b : Int := 10
def test8_Expected : Int := 5

-- Test case 9: Two negative numbers with odd sum
def test9_a : Int := -3
def test9_b : Int := -4
def test9_Expected : Int := -4

-- Test case 10: Large positive numbers
def test10_a : Int := 100
def test10_b : Int := 200
def test10_Expected : Int := 150

-- Recommend to validate: 1, 3, 4

end TestCases
