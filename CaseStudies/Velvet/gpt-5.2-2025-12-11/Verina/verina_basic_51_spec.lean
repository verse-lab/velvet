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
    BinarySearch: determine the insertion index for an integer `key` into a sorted array `a`.
    Natural language breakdown:
    1. Input is an array `a : Array Int` and a value `key : Int`.
    2. The array is assumed to be sorted in non-decreasing order.
    3. The output is an index `idx : Nat` between 0 and `a.size`.
    4. Every element strictly before `idx` is strictly less than `key`.
    5. Every element from `idx` onward (while in bounds) is greater than or equal to `key`.
    6. If `key` is larger than all elements, the result is `a.size`.
    7. This is the first position where `key` can be inserted while preserving sorted order.
-/

section Specs

-- Helper: non-decreasing sortedness for an Int array (index-based).
-- We keep it simple: all earlier indices have values ≤ later indices.
def isSortedNondecreasing (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

-- Helper: the lower-bound index characterized by a partition w.r.t. `key`.
-- This property is intended to uniquely determine the insertion index.
def isLowerBoundIndex (a : Array Int) (key : Int) (idx : Nat) : Prop :=
  idx ≤ a.size ∧
  (∀ (i : Nat), i < idx → a[i]! < key) ∧
  (∀ (i : Nat), idx ≤ i → i < a.size → key ≤ a[i]!)

-- Preconditions: array must be sorted non-decreasing.
def precondition (a : Array Int) (key : Int) : Prop :=
  isSortedNondecreasing a

-- Postconditions: result is a valid lower-bound insertion index.
def postcondition (a : Array Int) (key : Int) (result : Nat) : Prop :=
  isLowerBoundIndex a key result

end Specs

section Impl

method BinarySearch (a : Array Int) (key : Int)
  return (result : Nat)
  require precondition a key
  ensures postcondition a key result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: example from prompt, key present
-- a = [1,3,5,7,9], key=5 -> insertion index 2
-- IMPORTANT example

def test1_a : Array Int := #[1, 3, 5, 7, 9]

def test1_key : Int := 5

def test1_Expected : Nat := 2

-- Test case 2: key absent between elements
-- a = [1,3,5,7,9], key=6 -> insertion index 3
-- IMPORTANT example

def test2_a : Array Int := #[1, 3, 5, 7, 9]

def test2_key : Int := 6

def test2_Expected : Nat := 3

-- Test case 3: key smaller than all elements -> 0

def test3_a : Array Int := #[2, 4, 6, 8]

def test3_key : Int := 1

def test3_Expected : Nat := 0

-- Test case 4: key larger than all elements -> size

def test4_a : Array Int := #[2, 4, 6, 8]

def test4_key : Int := 10

def test4_Expected : Nat := 4

-- Test case 5: all elements equal to key -> first index 0
-- IMPORTANT example

def test5_a : Array Int := #[1, 1, 1, 1]

def test5_key : Int := 1

def test5_Expected : Nat := 0

-- Test case 6: duplicates with key between duplicate runs
-- a = [1,2,2,2,4], key=2 -> first index with a[i]≥2 is 1

def test6_a : Array Int := #[1, 2, 2, 2, 4]

def test6_key : Int := 2

def test6_Expected : Nat := 1

-- Test case 7: empty array -> size 0

def test7_a : Array Int := #[]

def test7_key : Int := 7

def test7_Expected : Nat := 0

-- Test case 8: single element, key less -> 0

def test8_a : Array Int := #[5]

def test8_key : Int := 4

def test8_Expected : Nat := 0

-- Test case 9: single element, key equal -> 0

def test9_a : Array Int := #[5]

def test9_key : Int := 5

def test9_Expected : Nat := 0

-- Recommend to validate: 1, 2, 5

end TestCases
