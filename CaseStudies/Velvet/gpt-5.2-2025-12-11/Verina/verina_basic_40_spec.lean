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
    secondSmallest: find the second-smallest number in an array of integers.
    Natural language breakdown:
    1. Input is an array `s` of integers.
    2. The array has at least two elements.
    3. There exist at least two distinct values in the array.
    4. The output is an element of the array.
    5. The output is strictly larger than the smallest value present in the array.
    6. Among all values in the array that are strictly larger than the minimum, the output is the least.
    7. The input array is not modified (functional setting: result depends only on `s`).
-/

section Specs

-- Helper: membership in an Array via a bounded Nat index
-- (Using Nat indices with `arr[i]!` as required by the guidelines.)
def InArray (s : Array Int) (x : Int) : Prop :=
  ∃ i : Nat, i < s.size ∧ s[i]! = x

-- Helper: x is a minimum value of the array
-- We keep this relational and computation-friendly (no finsets/min' required).
def IsMinVal (s : Array Int) (m : Int) : Prop :=
  InArray s m ∧ ∀ i : Nat, i < s.size → m ≤ s[i]!

-- Helper: x is the least value strictly above a given minimum m
-- This characterizes the second-smallest uniquely when it exists.
def IsSecondAboveMin (s : Array Int) (m : Int) (x : Int) : Prop :=
  InArray s x ∧ m < x ∧
    (∀ y : Int, InArray s y → m < y → x ≤ y)

-- Preconditions
-- 1) at least two elements
-- 2) there exist two distinct indices with different values (guarantees a strict minimum exists
--    and at least one value above it, hence a unique second-smallest).
def precondition (s : Array Int) : Prop :=
  s.size ≥ 2 ∧
  (∃ i : Nat, ∃ j : Nat,
    i < s.size ∧ j < s.size ∧ i ≠ j ∧ s[i]! ≠ s[j]!)

-- Postcondition: result is the least element strictly above the minimum element.
-- We existentially quantify the minimum value `m` to avoid committing to a specific implementation.
def postcondition (s : Array Int) (result : Int) : Prop :=
  ∃ m : Int, IsMinVal s m ∧ IsSecondAboveMin s m result

end Specs

section Impl

method secondSmallest (s : Array Int)
  return (result : Int)
  require precondition s
  ensures postcondition s result
  do
  pure 0  -- placeholder body

end Impl

section TestCases

-- Test case 1: example from prompt
-- s = #[5, 3, 1, 4, 2] -> second-smallest is 2

def test1_s : Array Int := #[5, 3, 1, 4, 2]
def test1_Expected : Int := 2

-- Test case 2: typical mixed order

def test2_s : Array Int := #[7, 2, 5, 3]
def test2_Expected : Int := 3

-- Test case 3: exactly two elements increasing

def test3_s : Array Int := #[10, 20]
def test3_Expected : Int := 20

-- Test case 4: exactly two elements decreasing

def test4_s : Array Int := #[20, 10]
def test4_Expected : Int := 20

-- Test case 5: small array

def test5_s : Array Int := #[3, 1, 2]
def test5_Expected : Int := 2

-- Test case 6: duplicates present but still at least two distinct values; second-smallest ignores extra mins

def test6_s : Array Int := #[1, 1, 2, 2, 3]
def test6_Expected : Int := 2

-- Test case 7: includes negative values

def test7_s : Array Int := #[-5, -1, -3, 0]
def test7_Expected : Int := -3

-- Test case 8: multiple occurrences of second-smallest value

def test8_s : Array Int := #[0, 2, 2, 1]
def test8_Expected : Int := 1

-- Test case 9: large range of values

def test9_s : Array Int := #[100, 50, 75, 25, 0]
def test9_Expected : Int := 25

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 6, 7

end TestCases
