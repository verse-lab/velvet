import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    rotateRight: Rotate a list of integers to the right by n positions
    Natural language breakdown:
    1. Given a list of integers l and a non-negative natural number n
    2. Rotate the list to the right by n positions
    3. Right rotation by n means each element moves n positions to the right
    4. Elements that would go past the end wrap around to the beginning
    5. The result has the same length as the input list
    6. The result contains the same elements as the input (is a permutation)
    7. For an empty list, return the empty list unchanged
    8. Right rotation by n is equivalent to left rotation by (length - n % length)
    9. Index relationship: result[i] = l[(i - n) mod length] for non-empty lists
       Equivalently: result[(i + n) mod length] = l[i]
-/

section Specs

-- Precondition: n is a natural number (always non-negative by type)
def precondition (l : List Int) (n : Nat) :=
  True

-- Postcondition: specifies the rotation relationship
-- For right rotation by n:
-- - The result has the same length as input
-- - Each element at position i in result comes from position (i - n) mod length in l
--   which is equivalent to: l[i] goes to position (i + n) mod length in result
def postcondition (l : List Int) (n : Nat) (result : List Int) :=
  result.length = l.length ∧
  (l.length = 0 → result = []) ∧
  (l.length > 0 →
    ∀ i : Nat, i < l.length →
      result[(i + n) % l.length]! = l[i]!)

end Specs

section Impl

method rotateRight (l : List Int) (n : Nat)
  return (result : List Int)
  require precondition l n
  ensures postcondition l n result
  do
  pure []

end Impl

section TestCases

-- Test case 1: Basic rotation by 2 (from problem description)
def test1_l : List Int := [1, 2, 3, 4, 5]
def test1_n : Nat := 2
def test1_Expected : List Int := [4, 5, 1, 2, 3]

-- Test case 2: Rotation larger than list length (n = 7, length = 5, 7 mod 5 = 2)
def test2_l : List Int := [1, 2, 3, 4, 5]
def test2_n : Nat := 7
def test2_Expected : List Int := [4, 5, 1, 2, 3]

-- Test case 3: No rotation (n = 0)
def test3_l : List Int := [1, 2, 3, 4, 5]
def test3_n : Nat := 0
def test3_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 4: Empty list
def test4_l : List Int := []
def test4_n : Nat := 2
def test4_Expected : List Int := []

-- Test case 5: Single element list
def test5_l : List Int := [42]
def test5_n : Nat := 5
def test5_Expected : List Int := [42]

-- Test case 6: Rotation by exact list length (full cycle)
def test6_l : List Int := [1, 2, 3, 4]
def test6_n : Nat := 4
def test6_Expected : List Int := [1, 2, 3, 4]

-- Test case 7: Rotation by 1
def test7_l : List Int := [1, 2, 3, 4, 5]
def test7_n : Nat := 1
def test7_Expected : List Int := [5, 1, 2, 3, 4]

-- Test case 8: List with negative integers
def test8_l : List Int := [-3, -2, -1, 0, 1, 2, 3]
def test8_n : Nat := 3
def test8_Expected : List Int := [1, 2, 3, -3, -2, -1, 0]

-- Test case 9: Two element list rotated by 1
def test9_l : List Int := [10, 20]
def test9_n : Nat := 1
def test9_Expected : List Int := [20, 10]

-- Test case 10: List with duplicate elements
def test10_l : List Int := [1, 1, 2, 2, 3, 3]
def test10_n : Nat := 2
def test10_Expected : List Int := [2, 3, 3, 1, 1, 2]

-- Recommend to validate: 1, 3, 4

end TestCases
