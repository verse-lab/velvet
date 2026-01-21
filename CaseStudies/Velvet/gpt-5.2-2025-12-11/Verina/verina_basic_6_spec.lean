import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    verina_basic_6: Minimum of three integers

    Natural language breakdown:
    1. The input consists of three integers a, b, and c.
    2. The function returns an integer result intended to be the minimum among a, b, and c.
    3. The result must be less than or equal to each input: result ≤ a, result ≤ b, and result ≤ c.
    4. The result must be one of the inputs: result = a or result = b or result = c.
    5. There are no rejected inputs; all Int inputs are valid.
-/

section Specs

-- No rejected inputs.
-- IMPORTANT: SpecDSL requires parameter names and order to match exactly between
-- precondition and the corresponding prefix of postcondition.
def precondition (a : Int) (b : Int) (c : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  (result ≤ a ∧ result ≤ b ∧ result ≤ c) ∧
  (result = a ∨ result = b ∨ result = c)

end Specs

section Impl

method minOfThree (a : Int) (b : Int) (c : Int)
  return (result : Int)
  require precondition a b c
  ensures postcondition a b c result
  do
  -- Placeholder body: must typecheck; correctness is deferred to the proof.
  pure a

end Impl

section TestCases

-- Test case 1: descending positives (given example)
def test1_a : Int := 3
def test1_b : Int := 2
def test1_c : Int := 1
def test1_Expected : Int := 1

-- Test case 2: all equal
def test2_a : Int := 5
def test2_b : Int := 5
def test2_c : Int := 5
def test2_Expected : Int := 5

-- Test case 3: distinct positives with first minimum
def test3_a : Int := 10
def test3_b : Int := 20
def test3_c : Int := 15
def test3_Expected : Int := 10

-- Test case 4: includes negative, first is minimum
def test4_a : Int := -1
def test4_b : Int := 2
def test4_c : Int := 3
def test4_Expected : Int := -1

-- Test case 5: includes negative, second is minimum
def test5_a : Int := 2
def test5_b : Int := -3
def test5_c : Int := 4
def test5_Expected : Int := -3

-- Test case 6: includes negative, third is minimum
def test6_a : Int := 2
def test6_b : Int := 3
def test6_c : Int := -5
def test6_Expected : Int := -5

-- Test case 7: zeros and positive
def test7_a : Int := 0
def test7_b : Int := 0
def test7_c : Int := 1
def test7_Expected : Int := 0

-- Test case 8: symmetric around zero
def test8_a : Int := 0
def test8_b : Int := -1
def test8_c : Int := 1
def test8_Expected : Int := -1

-- Test case 9: all negative
def test9_a : Int := -5
def test9_b : Int := -2
def test9_c : Int := -3
def test9_Expected : Int := -5

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test5, test9

end TestCases
