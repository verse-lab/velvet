import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    addTwoNumbers: Add two non-empty linked lists representing non-negative integers in reverse order.

    Natural language breakdown:
    1. Each input list represents a non-negative integer with digits in reverse order (least significant digit first)
    2. Each element in the lists is a single digit (0-9)
    3. The lists are non-empty
    4. The result should also be in reverse order (least significant digit first)
    5. The result represents the sum of the two input numbers
    6. No leading zeros in the representation, except for zero itself which is represented as [0]

    Mathematical formulation:
    - A list [d0, d1, d2, ...] represents the number d0 + d1*10 + d2*100 + ...
    - This is exactly Nat.ofDigits 10 applied to the list
    - The result list should represent the sum of the two input numbers
    - The result should be the canonical digit representation (valid digits, no leading zeros)

    Using Mathlib's Nat.ofDigits:
    - Nat.ofDigits b L converts a list of digits in little-endian order to a number
-/

section Specs

-- Helper: Check if a list represents valid digits (each element is 0-9)
def validDigits (l : List Nat) : Prop :=
  ∀ i : Nat, i < l.length → l[i]! < 10

-- Helper: Check if a digit list has no leading zeros (in reverse representation,
-- this means the last element is non-zero, unless the list is [0])
def noLeadingZeros (l : List Nat) : Prop :=
  l = [0] ∨ (l ≠ [] ∧ l.getLast! ≠ 0)

-- Precondition: Both lists are non-empty, contain valid digits, and have no leading zeros
def precondition (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1.length > 0 ∧
  l2.length > 0 ∧
  validDigits l1 ∧
  validDigits l2 ∧
  noLeadingZeros l1 ∧
  noLeadingZeros l2

-- Postcondition: The result represents the sum of the two input numbers
-- Specified relationally: the numeric value of result equals the sum of input values,
-- and result is in canonical form (valid digits, no leading zeros)
def postcondition (l1 : List Nat) (l2 : List Nat) (result : List Nat) : Prop :=
  -- The result represents the correct sum
  Nat.ofDigits 10 result = Nat.ofDigits 10 l1 + Nat.ofDigits 10 l2 ∧
  -- The result contains valid digits
  validDigits result ∧
  -- The result has no leading zeros (canonical form)
  noLeadingZeros result

end Specs

section Impl

method addTwoNumbers (l1 : List Nat) (l2 : List Nat)
  return (result : List Nat)
  require precondition l1 l2
  ensures postcondition l1 l2 result
  do
  pure [0]  -- placeholder

end Impl

section TestCases

-- Test case 1: Example from problem - 342 + 465 = 807
def test1_l1 : List Nat := [2, 4, 3]
def test1_l2 : List Nat := [5, 6, 4]
def test1_Expected : List Nat := [7, 0, 8]

-- Test case 2: 0 + 0 = 0
def test2_l1 : List Nat := [0]
def test2_l2 : List Nat := [0]
def test2_Expected : List Nat := [0]

-- Test case 3: Large numbers with carry propagation - 9999999 + 9999 = 10009998
def test3_l1 : List Nat := [9, 9, 9, 9, 9, 9, 9]
def test3_l2 : List Nat := [9, 9, 9, 9]
def test3_Expected : List Nat := [8, 9, 9, 9, 0, 0, 0, 1]

-- Test case 4: Different lengths - 321 + 54 = 375
def test4_l1 : List Nat := [1, 2, 3]
def test4_l2 : List Nat := [4, 5]
def test4_Expected : List Nat := [5, 7, 3]

-- Test case 5: Single digits - 5 + 5 = 10
def test5_l1 : List Nat := [5]
def test5_l2 : List Nat := [5]
def test5_Expected : List Nat := [0, 1]

-- Test case 6: No carry - 123 + 456 = 579
def test6_l1 : List Nat := [3, 2, 1]
def test6_l2 : List Nat := [6, 5, 4]
def test6_Expected : List Nat := [9, 7, 5]

-- Test case 7: Adding zero - 123 + 0 = 123
def test7_l1 : List Nat := [3, 2, 1]
def test7_l2 : List Nat := [0]
def test7_Expected : List Nat := [3, 2, 1]

-- Test case 8: Multiple carries - 999 + 1 = 1000
def test8_l1 : List Nat := [9, 9, 9]
def test8_l2 : List Nat := [1]
def test8_Expected : List Nat := [0, 0, 0, 1]

-- Recommend to validate: 1, 3, 5

end TestCases
