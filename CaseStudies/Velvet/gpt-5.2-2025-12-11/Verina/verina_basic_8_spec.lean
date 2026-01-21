import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    myMin: Determine the minimum of two integers.
    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. The output is an integer result.
    3. The result must be less than or equal to a, and less than or equal to b.
    4. The result must be one of the inputs (either a or b).
    5. When a = b, returning either one is allowed (they are equal).
-/

section Specs

-- No helper functions are necessary: we can specify the minimum using order and equality.

def precondition (a : Int) (b : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  result ≤ a ∧ result ≤ b ∧ (result = a ∨ result = b)

end Specs

section Impl

method myMin (a : Int) (b : Int) return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
    pure (min a b)  -- placeholder

end Impl

section TestCases

-- Test case 1: example (a = 3, b = 5)
def test1_a : Int := 3
def test1_b : Int := 5
def test1_Expected : Int := 3

-- Test case 2: a > b
def test2_a : Int := 10
def test2_b : Int := 7
def test2_Expected : Int := 7

-- Test case 3: a = b
def test3_a : Int := 4
def test3_b : Int := 4
def test3_Expected : Int := 4

-- Test case 4: negative and positive
def test4_a : Int := -3
def test4_b : Int := 5
def test4_Expected : Int := -3

-- Test case 5: positive and negative
def test5_a : Int := 3
def test5_b : Int := -5
def test5_Expected : Int := -5

-- Test case 6: both negative
def test6_a : Int := -3
def test6_b : Int := -5
def test6_Expected : Int := -5

-- Test case 7: zero and positive
def test7_a : Int := 0
def test7_b : Int := 10
def test7_Expected : Int := 0

-- Test case 8: zero and negative
def test8_a : Int := 0
def test8_b : Int := -10
def test8_Expected : Int := -10

-- Recommend to validate: 1, 3, 5

end TestCases
