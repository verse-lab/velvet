import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isGreater: determine if an integer is strictly greater than every element in an array
    Natural language breakdown:
    1. Inputs are an integer n and an array a of integers.
    2. The method returns a Boolean.
    3. The result is true exactly when n is strictly greater than every element in a.
    4. The result is false when there exists at least one element x in a with x ≥ n.
    5. Empty arrays are rejected (see reject input).
-/

section Specs

-- Preconditions: reject empty arrays.
def precondition (n : Int) (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: Boolean meaning of being strictly greater than every element.
-- We specify using index-wise comparison over the array.
def postcondition (n : Int) (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n))

end Specs

section Impl

method isGreater (n : Int) (a : Array Int)
  return (result : Bool)
  require precondition n a
  ensures postcondition n a result
  do
  -- Placeholder body only.
  pure true

end Impl

section TestCases

-- Test case 1: example provided (n larger than all elements)
def test1_n : Int := 6
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_Expected : Bool := true

-- Test case 2: n is not larger than all elements (some elements ≥ n)
def test2_n : Int := 3
def test2_a : Array Int := #[1, 2, 3, 4, 5]
def test2_Expected : Bool := false

-- Test case 3: equal elements, strictness matters
def test3_n : Int := 5
def test3_a : Array Int := #[5, 5, 5]
def test3_Expected : Bool := false

-- Test case 4: negatives, true case
def test4_n : Int := -1
def test4_a : Array Int := #[-10, -5, -3]
def test4_Expected : Bool := true

-- Test case 5: negatives, false due to element ≥ n
def test5_n : Int := -3
def test5_a : Array Int := #[-1, -2, -3]
def test5_Expected : Bool := false

-- Test case 6: includes 0, strictness against 0
def test6_n : Int := 0
def test6_a : Array Int := #[0, -1, -2]
def test6_Expected : Bool := false

-- Test case 7: unsorted array, true case
def test7_n : Int := 10
def test7_a : Array Int := #[1, 2, 9, 3]
def test7_Expected : Bool := true

-- Test case 8: single-element array, true
def test8_n : Int := 2
def test8_a : Array Int := #[1]
def test8_Expected : Bool := true

-- Test case 9: single-element array, false (equal)
def test9_n : Int := 1
def test9_a : Array Int := #[1]
def test9_Expected : Bool := false

-- Recommend to validate: test1, test2, test3

end TestCases
