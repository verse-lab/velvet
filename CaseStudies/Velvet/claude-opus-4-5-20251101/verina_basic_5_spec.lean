import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- multiply: Multiply two integers and return their product
--
-- Natural language breakdown:
-- 1. Given two integers a and b, compute their product a * b
-- 2. The result should handle all combinations of positive, negative, and zero values
-- 3. Multiplication of integers follows standard arithmetic rules:
--    - positive × positive = positive
--    - positive × negative = negative
--    - negative × positive = negative
--    - negative × negative = positive
--    - anything × zero = zero
-- 4. Use the built-in Int multiplication operation from Mathlib (Int.instMul)

section Specs

-- Precondition: No restrictions on input integers
def precondition (a : Int) (b : Int) :=
  True

-- Postcondition: The result is the product of a and b
def postcondition (a : Int) (b : Int) (result : Int) :=
  result = a * b

end Specs

section Impl

method multiply (a : Int) (b : Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: positive × positive (from problem examples)
def test1_a : Int := 3
def test1_b : Int := 4
def test1_Expected : Int := 12

-- Test case 2: positive × negative
def test2_a : Int := 3
def test2_b : Int := -4
def test2_Expected : Int := -12

-- Test case 3: negative × positive
def test3_a : Int := -3
def test3_b : Int := 4
def test3_Expected : Int := -12

-- Test case 4: negative × negative
def test4_a : Int := -3
def test4_b : Int := -4
def test4_Expected : Int := 12

-- Test case 5: zero × positive
def test5_a : Int := 0
def test5_b : Int := 5
def test5_Expected : Int := 0

-- Test case 6: positive × zero
def test6_a : Int := 5
def test6_b : Int := 0
def test6_Expected : Int := 0

-- Test case 7: zero × zero
def test7_a : Int := 0
def test7_b : Int := 0
def test7_Expected : Int := 0

-- Test case 8: larger positive numbers
def test8_a : Int := 100
def test8_b : Int := 25
def test8_Expected : Int := 2500

-- Test case 9: identity (multiply by 1)
def test9_a : Int := 42
def test9_b : Int := 1
def test9_Expected : Int := 42

-- Test case 10: multiply by -1
def test10_a : Int := 7
def test10_b : Int := -1
def test10_Expected : Int := -7

-- Recommend to validate: 1, 2, 4

end TestCases
