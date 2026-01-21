import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findSmallest: Find the smallest number in an array of natural numbers
    Natural language breakdown:
    1. We are given an array of natural numbers
    2. We need to find the minimum (smallest) element in the array
    3. If the array is empty, return none
    4. If the array is non-empty, return some(x) where x is the smallest element
    5. The result must satisfy:
       - When result is none: the array is empty
       - When result is some(x): x is in the array AND x is less than or equal to all elements in the array
    6. Edge cases:
       - Empty array: return none
       - Single element: return that element
       - All same elements: return that value
       - Multiple occurrences of minimum: return the minimum value
-/

section Specs

-- Helper definition: check if a value is in the array
def inArrayNat (arr : Array Nat) (val : Nat) : Prop :=
  ∃ i : Nat, i < arr.size ∧ arr[i]! = val

-- Postcondition: characterizes the smallest element
def ensures1 (s : Array Nat) (result : Option Nat) :=
  match result with
  | none => s.size = 0
  | some x =>
      -- x is in the array
      inArrayNat s x ∧
      -- x is less than or equal to all elements in the array
      (∀ i : Nat, i < s.size → x ≤ s[i]!)

def precondition (s : Array Nat) :=
  True  -- no preconditions

def postcondition (s : Array Nat) (result : Option Nat) :=
  ensures1 s result

end Specs

section Impl

method findSmallest (s : Array Nat)
  return (result : Option Nat)
  require precondition s
  ensures postcondition s result
  do
  pure none  -- placeholder

end Impl

section TestCases

-- Test case 1: Array with multiple elements including duplicates
def test1_s : Array Nat := #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
def test1_Expected : Option Nat := some 1

-- Test case 2: Array starting with minimum (0)
def test2_s : Array Nat := #[0, 1, 2, 3, 4, 5]
def test2_Expected : Option Nat := some 0

-- Test case 3: Single element array
def test3_s : Array Nat := #[1]
def test3_Expected : Option Nat := some 1

-- Test case 4: All same elements
def test4_s : Array Nat := #[10, 10, 10]
def test4_Expected : Option Nat := some 10

-- Test case 5: Minimum at the end
def test5_s : Array Nat := #[3, 2, 2, 2, 2, 2, 2, 1]
def test5_Expected : Option Nat := some 1

-- Test case 6: Single element array with 0
def test6_s : Array Nat := #[0]
def test6_Expected : Option Nat := some 0

-- Test case 7: Descending order array
def test7_s : Array Nat := #[100, 99, 98]
def test7_Expected : Option Nat := some 98

-- Test case 8: Empty array
def test8_s : Array Nat := #[]
def test8_Expected : Option Nat := none

-- Recommend to validate: 1, 3, 8

end TestCases

