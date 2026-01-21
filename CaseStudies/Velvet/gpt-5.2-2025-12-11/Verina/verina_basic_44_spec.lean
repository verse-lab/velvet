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
    isOddAtIndexOdd: verify that every odd index in an array of integers holds an odd integer.
    Natural language breakdown:
    1. Input is an array `a` of integers.
    2. Indices are natural numbers from 0 to `a.size - 1`.
    3. An index `i` is considered an odd index when `i % 2 = 1`.
    4. An integer value `x` is considered odd when `x % 2 ≠ 0`.
    5. The function returns true exactly when: for every valid index `i`, if `i` is odd then `a[i]!` is odd.
    6. If there exists a valid odd index whose element is not odd, the function returns false.
    7. There are no preconditions; the function must work for any input array.
    8. For an empty array, the condition is vacuously true.
-/

section Specs

-- Helper predicate: all elements at odd indices are odd.
-- We use the concrete index condition `i % 2 = 1` and the concrete Int oddness condition `x % 2 ≠ 0`.
-- Note: `i` is a Nat index, while `a[i]!` is an Int value.
def OddIndexElementsOdd (a : Array Int) : Prop :=
  ∀ (i : Nat), i < a.size → i % 2 = 1 → (a[i]!) % 2 ≠ 0

-- No preconditions.
def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Bool) : Prop :=
  result = true ↔ OddIndexElementsOdd a

end Specs

section Impl

method isOddAtIndexOdd (a : Array Int) return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
  pure true

end Impl

section TestCases

-- Test case 1: example from prompt
-- Odd indices are 1 and 3; elements are 2 and 4, which are not odd.
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Bool := false

-- Test case 2: all odd numbers; odd indices contain odd elements
-- Odd indices: 1 ↦ 3, 3 ↦ 7.
def test2_a : Array Int := #[1, 3, 5, 7, 9]
def test2_Expected : Bool := true

-- Test case 3: all even numbers; odd indices contain even elements
-- Odd indices: 1 ↦ 4, 3 ↦ 8.
def test3_a : Array Int := #[2, 4, 6, 8, 10]
def test3_Expected : Bool := false

-- Test case 4: empty array; vacuously true
def test4_a : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: single element; there are no odd indices
def test5_a : Array Int := #[7]
def test5_Expected : Bool := true

-- Test case 6: alternating even/odd so odd indices contain odd elements
def test6_a : Array Int := #[0, 1, 0, 1]
def test6_Expected : Bool := true

-- Test case 7: odd indices contain even elements
def test7_a : Array Int := #[0, 2, 4, 6]
def test7_Expected : Bool := false

-- Test case 8: includes negative odds at odd indices
-- Odd indices: 1 ↦ -3 (odd), 3 ↦ 5 (odd).
def test8_a : Array Int := #[2, -3, 4, 5]
def test8_Expected : Bool := true

-- Test case 9: size 2 array where index 1 exists and violates oddness
-- Odd index: 1 ↦ 0 (not odd).
def test9_a : Array Int := #[11, 0]
def test9_Expected : Bool := false

-- Recommend to validate: test1, test2, test4

end TestCases
