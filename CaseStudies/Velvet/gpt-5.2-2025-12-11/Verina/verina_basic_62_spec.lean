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
    Find: find the first occurrence index of a key in an integer array
    Natural language breakdown:
    1. Inputs are an array of integers `a` and an integer `key`.
    2. The output is an integer index of the first position where `key` occurs in `a`.
    3. If `key` does not occur in `a`, the output is -1.
    4. If the output is not -1, it must be a valid index: 0 ≤ result < a.size.
    5. If the output is not -1, then `a[Int.toNat result]! = key`.
    6. If the output is not -1, then every earlier position `j` with 0 ≤ j < result has `a[Int.toNat j]! ≠ key`.
    7. The array may be empty; there are no input preconditions.
-/

section Specs

-- Helper predicate: `result` is a valid found index of `key` in `a`.
-- Uses `Int.toNat` and explicit range constraints so that `a[...]!` is safe.
def FoundIndex (a : Array Int) (key : Int) (result : Int) : Prop :=
  0 ≤ result ∧
  (Int.toNat result) < a.size ∧
  a[(Int.toNat result)]! = key ∧
  ∀ (j : Int), 0 ≤ j ∧ j < result → a[(Int.toNat j)]! ≠ key

-- Helper predicate: key does not appear anywhere in the array.
def KeyAbsent (a : Array Int) (key : Int) : Prop :=
  ∀ (i : Nat), i < a.size → a[i]! ≠ key

-- No preconditions: array can be empty/non-empty; key arbitrary.
def precondition (a : Array Int) (key : Int) : Prop :=
  True

def postcondition (a : Array Int) (key : Int) (result : Int) : Prop :=
  (result = -1 ∧ KeyAbsent a key) ∨
  (result ≠ -1 ∧ FoundIndex a key result)

end Specs

section Impl

method Find (a: Array Int) (key: Int) return (result: Int)
  require precondition a key
  ensures postcondition a key result
  do
    pure (-1)  -- placeholder

end Impl

section TestCases

-- Test case 1: example from prompt
-- a = #[1,2,3,4,5], key = 3 -> first index is 2
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_key : Int := 3
def test1_Expected : Int := 2

-- Test case 2: key occurs multiple times; first occurrence is at index 0
def test2_a : Array Int := #[5, 7, 5, 9]
def test2_key : Int := 5
def test2_Expected : Int := 0

-- Test case 3: key not present in a non-empty array
def test3_a : Array Int := #[2, 4, 6, 8]
def test3_key : Int := 5
def test3_Expected : Int := (-1)

-- Test case 4: empty array always yields -1
def test4_a : Array Int := #[]
def test4_key : Int := 10
def test4_Expected : Int := (-1)

-- Test case 5: negative numbers; first occurrence is not at 0
def test5_a : Array Int := #[0, -3, -1, -3]
def test5_key : Int := (-3)
def test5_Expected : Int := 1

-- Test case 6: singleton array where key is present
def test6_a : Array Int := #[42]
def test6_key : Int := 42
def test6_Expected : Int := 0

-- Test case 7: singleton array where key is absent
def test7_a : Array Int := #[42]
def test7_key : Int := 0
def test7_Expected : Int := (-1)

-- Test case 8: key present at last index
def test8_a : Array Int := #[1, 1, 1, 2]
def test8_key : Int := 2
def test8_Expected : Int := 3

-- Test case 9: all elements match key; should return 0
def test9_a : Array Int := #[7, 7, 7]
def test9_key : Int := 7
def test9_Expected : Int := 0

-- Recommend to validate: 1, 5, 9

end TestCases
