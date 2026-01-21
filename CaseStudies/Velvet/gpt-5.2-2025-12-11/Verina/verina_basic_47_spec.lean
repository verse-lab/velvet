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
    arraySum: calculate the sum of all the elements in an array of integers.
    Natural language breakdown:
    1. Input is an Array Int named a.
    2. The method conceptually processes the entire array.
    3. The output is an Int equal to the total sum of all elements of a.
    4. The benchmark indicates empty arrays are rejected; therefore, we require a to be non-empty.
    5. For non-empty arrays, the sum is the standard additive sum of all elements.
-/

section Specs

-- Helper Functions
-- We use the standard `Array.sum` for an additive type with a zero.

-- Preconditions
-- Match REJECT_INPUTS: the empty array #[] is rejected.
-- Arrays are never null in Lean, so only non-emptiness is required.

def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postconditions
-- The result is uniquely determined as the array sum.

def postcondition (a : Array Int) (result : Int) : Prop :=
  result = a.sum

end Specs

section Impl

method arraySum (a : Array Int) return (result : Int)
  require precondition a
  ensures postcondition a result
  do
    pure 0  -- placeholder body

end Impl

section TestCases

-- Test case 1: example from prompt
-- a = #[1,2,3,4,5] => 15

def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Int := 15

-- Test case 2: example from prompt

def test2_a : Array Int := #[13, 14, 15, 16, 17]
def test2_Expected : Int := 75

-- Test case 3: example from prompt (all negative)

def test3_a : Array Int := #[-1, -2, -3]
def test3_Expected : Int := -6

-- Test case 4: example from prompt (cancelling)

def test4_a : Array Int := #[10, -10]
def test4_Expected : Int := 0

-- Test case 5: single element

def test5_a : Array Int := #[42]
def test5_Expected : Int := 42

-- Test case 6: contains zeros

def test6_a : Array Int := #[0, 0, 7, 0]
def test6_Expected : Int := 7

-- Test case 7: mixed positives and negatives

def test7_a : Array Int := #[3, -1, 4, -5, 9]
def test7_Expected : Int := 10

-- Test case 8: larger magnitude Ints

def test8_a : Array Int := #[1000000, -999999, 2]
def test8_Expected : Int := 3

-- Test case 9: non-empty edge case (minimal size = 1, negative)

def test9_a : Array Int := #[-7]
def test9_Expected : Int := -7

-- Recommend to validate: 1, 3, 4

end TestCases
