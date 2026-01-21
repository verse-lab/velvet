import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isSublist: Determine whether one list is a contiguous sublist (infix) of another
    Natural language breakdown:
    1. We have two input lists of integers: sub (potential sublist) and main (list to search in)
    2. A contiguous sublist (infix) means sub appears as consecutive elements within main
    3. The function returns true if sub is an infix of main, false otherwise
    4. An empty list is always a contiguous sublist of any list (returns true)
    5. A non-empty list cannot be a contiguous sublist of an empty list (returns false)
    6. The infix relation is captured by List.IsInfix (<:+:) in Mathlib/Lean
    7. List.IsInfix l₁ l₂ means there exist lists s and t such that l₂ = s ++ l₁ ++ t
    8. No preconditions needed - both lists can be any valid lists of integers
-/

section Specs

-- Helper Functions

-- Using the standard IsInfix relation from Lean/Mathlib
-- List.IsInfix l₁ l₂ (written l₁ <:+: l₂) means l₁ appears as a contiguous subsequence in l₂

-- Postcondition: result is true iff sub is an infix of main
def ensures1 (sub : List Int) (main : List Int) (result : Bool) :=
  result = true ↔ sub <:+: main

def precondition (sub : List Int) (main : List Int) :=
  True  -- no preconditions

def postcondition (sub : List Int) (main : List Int) (result : Bool) :=
  ensures1 sub main result

end Specs

section Impl

method isSublist (sub : List Int) (main : List Int)
  return (result : Bool)
  require precondition sub main
  ensures postcondition sub main result
  do
  pure false  -- placeholder

end Impl

section TestCases

-- Test case 1: [1, 2] is a contiguous sublist of [3, 1, 2, 4]
def test1_sub : List Int := [1, 2]
def test1_main : List Int := [3, 1, 2, 4]
def test1_Expected : Bool := true

-- Test case 2: [2, 3] is NOT a contiguous sublist of [3, 1, 2, 4]
def test2_sub : List Int := [2, 3]
def test2_main : List Int := [3, 1, 2, 4]
def test2_Expected : Bool := false

-- Test case 3: [3, 1] is a contiguous sublist of [3, 1, 2, 4] (at beginning)
def test3_sub : List Int := [3, 1]
def test3_main : List Int := [3, 1, 2, 4]
def test3_Expected : Bool := true

-- Test case 4: [4] is a contiguous sublist of [3, 1, 2, 4] (at end)
def test4_sub : List Int := [4]
def test4_main : List Int := [3, 1, 2, 4]
def test4_Expected : Bool := true

-- Test case 5: [5] is NOT a contiguous sublist of [3, 1, 2, 4] (element not present)
def test5_sub : List Int := [5]
def test5_main : List Int := [3, 1, 2, 4]
def test5_Expected : Bool := false

-- Test case 6: Empty list is a contiguous sublist of any list
def test6_sub : List Int := []
def test6_main : List Int := [3, 1, 2, 4]
def test6_Expected : Bool := true

-- Test case 7: Non-empty list is NOT a contiguous sublist of empty list
def test7_sub : List Int := [1, 2]
def test7_main : List Int := []
def test7_Expected : Bool := false

-- Test case 8: Empty list is a contiguous sublist of empty list
def test8_sub : List Int := []
def test8_main : List Int := []
def test8_Expected : Bool := true

-- Test case 9: Full list is a contiguous sublist of itself
def test9_sub : List Int := [3, 1, 2, 4]
def test9_main : List Int := [3, 1, 2, 4]
def test9_Expected : Bool := true

-- Recommend to validate: 1, 2, 6

end TestCases
