import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isOddAtIndexOdd: Verify if every odd index in an array of integers holds an odd number
    Natural language breakdown:
    1. We have an array of integers as input
    2. We need to check indices that are odd (1, 3, 5, 7, ...)
    3. For each odd index i, the element at that index must be odd
    4. An integer is odd if it is not divisible by 2
    5. Return true if all odd indices contain odd numbers
    6. Return false if there exists at least one odd index with an even number
    7. Edge case: Empty array returns true (vacuously true - no odd indices exist)
    8. Edge case: Single element array returns true (index 0 is even, so no odd indices to check)
    9. No preconditions - works for any array of integers
-/

section Specs

-- Helper function to check if an integer is odd
-- Using the standard definition: odd means not even (not divisible by 2)
def isOddInt (n : Int) : Prop := Odd n

-- Property: all odd indices in the array contain odd integers
def allOddIndicesHaveOddValues (a : Array Int) : Prop :=
  ∀ i : Nat, i < a.size → Odd i → Odd (a[i]!)

-- Postcondition: result is true iff all odd indices contain odd values
def ensures1 (a : Array Int) (result : Bool) : Prop :=
  result = true ↔ allOddIndicesHaveOddValues a

def precondition (a : Array Int) : Prop :=
  True  -- no preconditions

def postcondition (a : Array Int) (result : Bool) : Prop :=
  ensures1 a result

end Specs

section Impl

method isOddAtIndexOdd (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
  pure true  -- placeholder

end Impl

section TestCases

-- Test case 1: Array with even numbers at odd indices (from problem example)
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Bool := false

-- Test case 2: All odd numbers - odd indices have odd values
def test2_a : Array Int := #[1, 3, 5, 7, 9]
def test2_Expected : Bool := true

-- Test case 3: All even numbers - odd indices have even values
def test3_a : Array Int := #[2, 4, 6, 8, 10]
def test3_Expected : Bool := false

-- Test case 4: Empty array - vacuously true
def test4_a : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: Single element array - no odd indices to check
def test5_a : Array Int := #[7]
def test5_Expected : Bool := true

-- Test case 6: Alternating pattern where odd indices have odd values
def test6_a : Array Int := #[0, 1, 0, 1]
def test6_Expected : Bool := true

-- Test case 7: Even numbers at odd indices
def test7_a : Array Int := #[0, 2, 4, 6]
def test7_Expected : Bool := false

-- Test case 8: Two elements with odd at index 1
def test8_a : Array Int := #[2, 5]
def test8_Expected : Bool := true

-- Test case 9: Negative odd numbers at odd indices
def test9_a : Array Int := #[0, -3, 0, -5]
def test9_Expected : Bool := true

-- Test case 10: Mixed with negative even at odd index
def test10_a : Array Int := #[1, -4, 3, 5]
def test10_Expected : Bool := false

-- Recommend to validate: 1, 2, 4

end TestCases
