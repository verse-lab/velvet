import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isSorted: check whether an array of integers is sorted in non-decreasing order.
    Natural language breakdown:
    1. Input is an array of integers `a`; it may be empty or any length.
    2. The result is a boolean.
    3. The result is true exactly when every adjacent pair is ordered: for each index i with i+1 in bounds,
       we have a[i] ≤ a[i+1].
    4. When the result is true, the array is globally non-decreasing: for any indices i < j within bounds,
       a[i] ≤ a[j].
    5. When the result is false, the array is not adjacent-sorted, meaning there exists some adjacent inversion.
-/

section Specs

-- Adjacent non-decreasing order.
-- Using Nat indices and `a[i]!` with explicit bounds checks.
def AdjacentSorted (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

-- Global non-decreasing order (matches the Note text).
def GloballySorted (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

-- No input restrictions.
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) The boolean result reflects adjacent sortedness.
-- 2) If true, also satisfies the global non-decreasing guarantee.
-- 3) If false, then adjacent sortedness does not hold.
def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ AdjacentSorted a) ∧
  (result = true → GloballySorted a) ∧
  (result = false ↔ ¬ AdjacentSorted a)

end Specs

section Impl

method isSorted (a : Array Int) return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
    pure true

end Impl

section TestCases

-- Test case 1: example from prompt, already sorted
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Bool := true

-- Test case 2: strictly decreasing
def test2_a : Array Int := #[5, 4, 3, 2, 1]
def test2_Expected : Bool := false

-- Test case 3: one local inversion in the middle
def test3_a : Array Int := #[1, 3, 2, 4, 5]
def test3_Expected : Bool := false

-- Test case 4: empty array (vacuously sorted)
def test4_a : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: singleton array (vacuously sorted)
def test5_a : Array Int := #[10]
def test5_Expected : Bool := true

-- Test case 6: all equal elements (non-decreasing)
def test6_a : Array Int := #[2, 2, 2, 2]
def test6_Expected : Bool := true

-- Test case 7: has equal neighbors and increasing steps
def test7_a : Array Int := #[1, 2, 2, 3]
def test7_Expected : Bool := true

-- Test case 8: minimal unsorted length-2 array
def test8_a : Array Int := #[2, 1]
def test8_Expected : Bool := false

-- Test case 9: sorted with negatives and duplicates
def test9_a : Array Int := #[-3, -3, -1, 0, 0, 2]
def test9_Expected : Bool := true

-- Recommend to validate: 1, 3, 4

end TestCases
