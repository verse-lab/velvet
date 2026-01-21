import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    containsConsecutiveNumbers: determine whether an array of integers contains at least one pair of consecutive numbers
    Natural language breakdown:
    1. Input is an array `a` of integers; it may be empty or non-empty.
    2. A "consecutive pair" means there exists an index `i` such that `i + 1 < a.size` and `a[i] + 1 = a[i+1]`.
    3. The result is `true` iff such an index exists.
    4. If the array has size 0 or 1, then no such index exists and the result is `false`.
    5. There are no preconditions.
-/

section Specs

-- Helper predicate: there exists an adjacent index with successor-by-1 relation.
-- Using Nat indices with bounds and `a[i]!` access as required by the guidelines.
def HasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!

-- No preconditions.
def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: result is true exactly when the array has a consecutive pair.
def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ HasConsecutivePair a)

end Specs

section Impl

method containsConsecutiveNumbers (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
  pure false

end Impl

section TestCases

-- Test case 1: example from prompt
def test1_a : Array Int := #[1, 2, 3, 5]
def test1_Expected : Bool := true

-- Test case 2: no consecutive numbers
def test2_a : Array Int := #[1, 3, 5, 7]
def test2_Expected : Bool := false

-- Test case 3: empty array
def test3_a : Array Int := #[]
def test3_Expected : Bool := false

-- Test case 4: single element
def test4_a : Array Int := #[10]
def test4_Expected : Bool := false

-- Test case 5: minimal positive case (two elements consecutive)
def test5_a : Array Int := #[5, 6]
def test5_Expected : Bool := true

-- Test case 6: consecutive pair occurs in the middle
def test6_a : Array Int := #[5, 7, 8, 10]
def test6_Expected : Bool := true

-- Test case 7: duplicates then consecutive (9,9,10 has 9+1=10)
def test7_a : Array Int := #[9, 9, 10]
def test7_Expected : Bool := true

-- Test case 8: all equal, no consecutive increment
def test8_a : Array Int := #[3, 3, 3]
def test8_Expected : Bool := false

-- Recommend to validate: 1, 3, 7

end TestCases
