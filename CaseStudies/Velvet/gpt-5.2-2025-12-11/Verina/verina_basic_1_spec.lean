import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    hasOppositeSign: determine whether two integers have opposite signs.

    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. Zero is considered neither positive nor negative.
    3. Two integers have opposite signs exactly when one is strictly positive
       and the other is strictly negative.
    4. Equivalently, both must be nonzero and their signs (via Int.sign)
       must be different and opposite.
    5. Int.sign x = 1 if x > 0; Int.sign x = -1 if x < 0; Int.sign x = 0 if x = 0.
    6. The method should return true iff a and b have opposite signs.
    7. It should return false if both are nonnegative, both are nonpositive,
       or if at least one is zero.

    We formalize this using inequalities on Int.
-/

section Specs

@[loomAbstractionSimp]
def hasOppositeSignSpec (a: Int) (b: Int) : Prop :=
  (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)

end Specs

section Impl

method hasOppositeSign (a: Int) (b: Int)
  return (result: Bool)
  ensures result = true ↔ hasOppositeSignSpec a b
  do
  pure false  -- placeholder implementation

end Impl

section TestCases

-- Test case 1: example with a negative and a positive integer (-5, 10) → true
-- (taken from the original problem's first example)
def test1_a : Int := -5
def test1_b : Int := 10
def test1_Expected : Bool := true

-- Test case 2: positive and negative reversed (5, -10) → true
def test2_a : Int := 5
def test2_b : Int := -10
def test2_Expected : Bool := true

-- Test case 3: both positive (5, 10) → false
def test3_a : Int := 5
def test3_b : Int := 10
def test3_Expected : Bool := false

-- Test case 4: both negative (-5, -10) → false
def test4_a : Int := -5
def test4_b : Int := -10
def test4_Expected : Bool := false

-- Test case 5: one zero, one positive (0, 10) → false
def test5_a : Int := 0
def test5_b : Int := 10
def test5_Expected : Bool := false

-- Test case 6: one zero, one negative (0, -10) → false
def test6_a : Int := 0
def test6_b : Int := -10
def test6_Expected : Bool := false

-- Test case 7: both zero (0, 0) → false
def test7_a : Int := 0
def test7_b : Int := 0
def test7_Expected : Bool := false

-- Test case 8: small magnitude opposite signs (-1, 1) → true
def test8_a : Int := -1
def test8_b : Int := 1
def test8_Expected : Bool := true

end TestCases

-- Recommend to validate: 1, 2, 3, 5, 7, 8
