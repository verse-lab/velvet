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
    rotateRight: Rotate a list of integers to the right by n positions.
    Natural language breakdown:
    1. Inputs are a list l : List Int and a rotation amount n : Nat.
    2. Rotating to the right by k means elements shift right; elements that pass the end reappear at the front.
    3. Rotation is cyclic and depends only on k modulo l.length.
    4. The output list must have the same length as l.
    5. If l is empty, rotating yields the empty list.
    6. For a nonempty list l with length m and r := n % m, the element at output index i equals
       the element at input index (i + (m - r)) % m.
-/

section Specs

-- Helper: index-based characterization of a right rotation.
-- We use Nat indexing with get! and explicit bounds.
-- For the empty list, the result must be empty.
def isRotateRight (l : List Int) (n : Nat) (result : List Int) : Prop :=
  result.length = l.length ∧
  (l = [] → result = []) ∧
  (l ≠ [] →
    let m := l.length
    let r := n % m
    ∀ i : Nat, i < m →
      result[i]! = l[(i + (m - r)) % m]!)

-- Preconditions
-- n : Nat is already non-negative.
def precondition (l : List Int) (n : Nat) : Prop :=
  True

-- Postconditions
-- The result is uniquely characterized by length + index mapping (for nonempty) and empty-list behavior.
def postcondition (l : List Int) (n : Nat) (result : List Int) : Prop :=
  isRotateRight l n result

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

-- Test case 1: example from prompt
-- rotateRight([1,2,3,4,5], 2) = [4,5,1,2,3]
def test1_l : List Int := [1, 2, 3, 4, 5]
def test1_n : Nat := 2
def test1_Expected : List Int := [4, 5, 1, 2, 3]

-- Test case 2: rotation larger than length (uses modulo)
def test2_l : List Int := [1, 2, 3, 4, 5]
def test2_n : Nat := 7
def test2_Expected : List Int := [4, 5, 1, 2, 3]

-- Test case 3: zero rotation
def test3_l : List Int := [1, 2, 3, 4, 5]
def test3_n : Nat := 0
def test3_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 4: empty list remains empty
def test4_l : List Int := []
def test4_n : Nat := 2
def test4_Expected : List Int := []

-- Test case 5: single-element list is unchanged for any n
def test5_l : List Int := [42]
def test5_n : Nat := 123
def test5_Expected : List Int := [42]

-- Test case 6: n is multiple of length
def test6_l : List Int := [10, -1, 7]
def test6_n : Nat := 3
def test6_Expected : List Int := [10, -1, 7]

-- Test case 7: rotate by 1
def test7_l : List Int := [10, -1, 7]
def test7_n : Nat := 1
def test7_Expected : List Int := [7, 10, -1]

-- Test case 8: list with duplicates
def test8_l : List Int := [2, 2, 3, 2]
def test8_n : Nat := 2
def test8_Expected : List Int := [3, 2, 2, 2]

-- Test case 9: two-element list, large n
def test9_l : List Int := [-5, 9]
def test9_n : Nat := 5
def test9_Expected : List Int := [9, -5]

-- Recommend to validate: test1, test2, test4

end TestCases
