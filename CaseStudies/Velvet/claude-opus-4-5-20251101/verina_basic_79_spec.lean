import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    onlineMax: Given an array and index x, find the maximum of first x elements and
    the first index >= x where an element exceeds that maximum (or last index if none exists)
    
    Natural language breakdown:
    1. We are given a nonempty array of integers and a valid index x with 1 ≤ x < a.size
    2. We need to compute two values: m (maximum of first x elements) and p (an index)
    3. m is the maximum value among elements a[0], a[1], ..., a[x-1]
    4. For p: search from index x to the end of the array
    5. If there exists an element a[i] (where i >= x) that is strictly greater than m,
       then p is the smallest such index
    6. If no such element exists, p is set to a.size - 1 (the last valid index)
    7. The output is the pair (m, p)
    
    Key properties:
    - m must equal the maximum of the first x elements
    - p must be in range [x, a.size)
    - If a[p]! > m and p >= x, then p is the first such index (no earlier index >= x has this property)
    - If no element from index x onward exceeds m, then p = a.size - 1
-/

section Specs

-- Helper: check if m is the maximum of the first x elements
def isMaxOfFirstX (a : Array Int) (x : Nat) (m : Int) : Prop :=
  (∃ i : Nat, i < x ∧ a[i]! = m) ∧
  (∀ i : Nat, i < x → a[i]! ≤ m)

-- Helper: check if there exists an element from index x onward that exceeds m
def existsExceedingM (a : Array Int) (x : Nat) (m : Int) : Prop :=
  ∃ i : Nat, x ≤ i ∧ i < a.size ∧ a[i]! > m

-- Helper: p is the first index >= x where a[p] > m
def isFirstExceedingIndex (a : Array Int) (x : Nat) (m : Int) (p : Nat) : Prop :=
  x ≤ p ∧ p < a.size ∧ a[p]! > m ∧ (∀ j : Nat, x ≤ j → j < p → a[j]! ≤ m)

-- Precondition: array is nonempty and x is valid (1 ≤ x < a.size)
def precondition (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ 1 ≤ x ∧ x < a.size

-- Postcondition: m is max of first x elements, p is determined by the ordering condition
def postcondition (a : Array Int) (x : Nat) (result : Int × Nat) : Prop :=
  let m := result.1
  let p := result.2
  -- m is the maximum of the first x elements
  isMaxOfFirstX a x m ∧
  -- p is in valid range [x, a.size)
  x ≤ p ∧ p < a.size ∧
  -- Either p is the first index >= x where a[p] > m, or no such index exists and p = a.size - 1
  ((existsExceedingM a x m ∧ isFirstExceedingIndex a x m p) ∨
   (¬existsExceedingM a x m ∧ p = a.size - 1))

end Specs

section Impl

method onlineMax (a : Array Int) (x : Nat)
  return (result : Int × Nat)
  require precondition a x
  ensures postcondition a x result
  do
  pure (0, 0)  -- placeholder

end Impl

section TestCases

-- Test case 1: a = #[3, 7, 5, 2, 9], x = 3
-- Max of first 3 elements [3, 7, 5] is 7
-- From index 3: a[3] = 2 ≤ 7, a[4] = 9 > 7, so p = 4
def test1_a : Array Int := #[3, 7, 5, 2, 9]
def test1_x : Nat := 3
def test1_Expected : Int × Nat := (7, 4)

-- Test case 2: a = #[10, 10, 5, 1], x = 2
-- Max of first 2 elements [10, 10] is 10
-- From index 2: a[2] = 5 ≤ 10, a[3] = 1 ≤ 10, no element exceeds 10, so p = 3
def test2_a : Array Int := #[10, 10, 5, 1]
def test2_x : Nat := 2
def test2_Expected : Int × Nat := (10, 3)

-- Test case 3: a = #[1, 3, 3, 3, 1], x = 2
-- Max of first 2 elements [1, 3] is 3
-- From index 2: a[2] = 3 ≤ 3, a[3] = 3 ≤ 3, a[4] = 1 ≤ 3, no element exceeds 3, so p = 4
def test3_a : Array Int := #[1, 3, 3, 3, 1]
def test3_x : Nat := 2
def test3_Expected : Int × Nat := (3, 4)

-- Test case 4: a = #[5, 4, 4, 6, 2], x = 2
-- Max of first 2 elements [5, 4] is 5
-- From index 2: a[2] = 4 ≤ 5, a[3] = 6 > 5, so p = 3
def test4_a : Array Int := #[5, 4, 4, 6, 2]
def test4_x : Nat := 2
def test4_Expected : Int × Nat := (5, 3)

-- Test case 5: a = #[2, 8, 7, 7, 7], x = 3
-- Max of first 3 elements [2, 8, 7] is 8
-- From index 3: a[3] = 7 ≤ 8, a[4] = 7 ≤ 8, no element exceeds 8, so p = 4
def test5_a : Array Int := #[2, 8, 7, 7, 7]
def test5_x : Nat := 3
def test5_Expected : Int × Nat := (8, 4)

-- Test case 6: Edge case - x = 1 (minimum valid x)
-- a = #[5, 10], x = 1
-- Max of first 1 element [5] is 5
-- From index 1: a[1] = 10 > 5, so p = 1
def test6_a : Array Int := #[5, 10]
def test6_x : Nat := 1
def test6_Expected : Int × Nat := (5, 1)

-- Test case 7: All elements equal
-- a = #[7, 7, 7, 7], x = 2
-- Max of first 2 elements [7, 7] is 7
-- From index 2: a[2] = 7 ≤ 7, a[3] = 7 ≤ 7, no element exceeds 7, so p = 3
def test7_a : Array Int := #[7, 7, 7, 7]
def test7_x : Nat := 2
def test7_Expected : Int × Nat := (7, 3)

-- Test case 8: Negative numbers
-- a = #[-5, -3, -10, -2], x = 2
-- Max of first 2 elements [-5, -3] is -3
-- From index 2: a[2] = -10 ≤ -3, a[3] = -2 > -3, so p = 3
def test8_a : Array Int := #[-5, -3, -10, -2]
def test8_x : Nat := 2
def test8_Expected : Int × Nat := (-3, 3)

-- Test case 9: First element after x exceeds max
-- a = #[1, 2, 5, 3], x = 2
-- Max of first 2 elements [1, 2] is 2
-- From index 2: a[2] = 5 > 2, so p = 2
def test9_a : Array Int := #[1, 2, 5, 3]
def test9_x : Nat := 2
def test9_Expected : Int × Nat := (2, 2)

-- Test case 10: Large gap between max and exceeding element
-- a = #[100, 50, 1, 1, 1, 200], x = 2
-- Max of first 2 elements [100, 50] is 100
-- From index 2: a[2]=1, a[3]=1, a[4]=1, a[5]=200 > 100, so p = 5
def test10_a : Array Int := #[100, 50, 1, 1, 1, 200]
def test10_x : Nat := 2
def test10_Expected : Int × Nat := (100, 5)

-- Recommend to validate: 1, 4, 6

end TestCases
