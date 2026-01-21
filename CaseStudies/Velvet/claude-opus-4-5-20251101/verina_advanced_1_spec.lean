import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- FindSingleNumber: Find the unique element that appears exactly once in a list where all other elements appear exactly twice
--
-- Natural language breakdown:
-- 1. We are given a non-empty list of integers
-- 2. Every element in the list appears exactly twice, except for one element that appears exactly once
-- 3. We need to find and return that unique element that appears only once
-- 4. The precondition ensures the list satisfies this property (one element appears once, all others appear twice)
-- 5. The postcondition ensures the returned result is the element that appears exactly once
-- 6. Using List.count from Mathlib to count occurrences of elements
-- 7. The classic XOR solution works because a ⊕ a = 0 and a ⊕ 0 = a, so all pairs cancel out

section Specs

-- Predicate: the list has valid structure (one element once, all others twice)
def hasValidSingleNumberProperty (nums : List Int) : Prop :=
  nums.length > 0 ∧
  (∃! x, x ∈ nums ∧ nums.count x = 1) ∧
  (∀ x, x ∈ nums → nums.count x = 1 ∨ nums.count x = 2)

-- Predicate: result is the unique element appearing exactly once
def isSingleNumber (nums : List Int) (result : Int) : Prop :=
  result ∈ nums ∧ nums.count result = 1

-- Precondition: list must have valid single number property
def precondition (nums : List Int) :=
  hasValidSingleNumberProperty nums

-- Postcondition: result is the element appearing exactly once
def postcondition (nums : List Int) (result : Int) :=
  isSingleNumber nums result

end Specs

section Impl

method FindSingleNumber (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
    pure 0

end Impl

section TestCases

-- Test case 1: [2, 2, 3] -> 3 (from problem example)
def test1_nums : List Int := [2, 2, 3]
def test1_Expected : Int := 3

-- Test case 2: [1, 2, 2] -> 1 (from problem example)
def test2_nums : List Int := [1, 2, 2]
def test2_Expected : Int := 1

-- Test case 3: [3, 3, 4, 4, 1] -> 1 (from problem example)
def test3_nums : List Int := [3, 3, 4, 4, 1]
def test3_Expected : Int := 1

-- Test case 4: [0, 1, 3, 1, 3, 88, 88, 100, 100] -> 0 (zero as single number)
def test4_nums : List Int := [0, 1, 3, 1, 3, 88, 88, 100, 100]
def test4_Expected : Int := 0

-- Test case 5: [-1, -1, 7, 9, 7] -> 9 (negative numbers present)
def test5_nums : List Int := [-1, -1, 7, 9, 7]
def test5_Expected : Int := 9

-- Test case 6: single element list
def test6_nums : List Int := [42]
def test6_Expected : Int := 42

-- Test case 7: single number at the beginning
def test7_nums : List Int := [5, 1, 1, 2, 2]
def test7_Expected : Int := 5

-- Test case 8: negative single number
def test8_nums : List Int := [-5, 3, 3]
def test8_Expected : Int := -5

-- Recommend to validate: 1, 3, 6

end TestCases
