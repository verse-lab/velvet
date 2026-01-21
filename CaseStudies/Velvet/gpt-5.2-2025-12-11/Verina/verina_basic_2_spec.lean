import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import Batteries.Data.Array.Basic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findSmallest: Find the smallest number in an array of natural numbers
    Natural language breakdown:
    1. Given an array of natural numbers, find the smallest element
    2. If the array is empty, return none
    3. If the array is non-empty, return some(min) where min is the smallest element
    4. The smallest element must be in the array
    5. The smallest element must be less than or equal to all other elements
    6. For non-empty arrays, the result uniquely identifies the minimum value
    7. This is a property-based specification: we specify what the minimum must satisfy
       (membership and minimality), not how to compute it
    8. Edge cases:
       - Empty array: return none
       - Single element: return that element
       - All equal elements: return that common value
       - Array with duplicates of minimum: return the minimum value
-/

section Specs

-- Precondition: no requirements on input array
def precondition (s : Array Nat) :=
  True

-- Postcondition: characterize the result based on array emptiness
def postcondition (s : Array Nat) (result : Option Nat) :=
  match result with
  | none => s.size = 0
  | some min =>
      s.size > 0 ∧
      (∃ i, i < s.size ∧ s[i]! = min) ∧
      (∀ j, j < s.size → min ≤ s[j]!)

end Specs

section Impl

method findSmallest (s: Array Nat)
  return (result: Option Nat)
  require precondition s
  ensures postcondition s result
  do
  pure none

end Impl

section TestCases

-- Test case 1: Example from problem - array with duplicates
def test1_s : Array Nat := #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
def test1_Expected : Option Nat := some 1

-- Test case 2: Minimum at start (zero)
def test2_s : Array Nat := #[0, 1, 2, 3, 4, 5]
def test2_Expected : Option Nat := some 0

-- Test case 3: Single element array
def test3_s : Array Nat := #[1]
def test3_Expected : Option Nat := some 1

-- Test case 4: All elements the same
def test4_s : Array Nat := #[10, 10, 10]
def test4_Expected : Option Nat := some 10

-- Test case 5: Minimum at end
def test5_s : Array Nat := #[3, 2, 2, 2, 2, 2, 2, 1]
def test5_Expected : Option Nat := some 1

-- Test case 6: Single zero
def test6_s : Array Nat := #[0]
def test6_Expected : Option Nat := some 0

-- Test case 7: Descending order, minimum at end
def test7_s : Array Nat := #[100, 99, 98]
def test7_Expected : Option Nat := some 98

-- Test case 8: Empty array
def test8_s : Array Nat := #[]
def test8_Expected : Option Nat := none

-- Recommend to validate: 1, 7, 8

end TestCases
