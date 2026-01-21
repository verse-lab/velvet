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
    findProduct: product of the first even and the first odd integer encountered in a list
    Natural language breakdown:
    1. Input is a list of integers `lst`.
    2. We scan `lst` from left to right.
    3. The "first even" is the leftmost element of `lst` whose remainder modulo 2 is 0.
    4. The "first odd" is the leftmost element of `lst` whose remainder modulo 2 is not 0.
    5. The output is the product (in `Int`) of these two first elements.
    6. Precondition: `lst` contains at least one even integer and at least one odd integer.
    7. The result must equal (firstEven * firstOdd) where each is the respective leftmost witness.
-/

section Specs

-- Helper predicates as Bool for use with `List.find?`.
-- We define parity via `Int` modulo and boolean equality.

def isEven (z : Int) : Bool := (z % 2) == 0

def isOdd (z : Int) : Bool := (z % 2) != 0

-- Precondition: at least one even and at least one odd exists in the list.
-- Using `find?` makes the "first" (leftmost) notion precise.

def precondition (lst : List Int) : Prop :=
  (lst.find? isEven).isSome ∧ (lst.find? isOdd).isSome

-- Postcondition: result is the product of the first even and the first odd found.

def postcondition (lst : List Int) (result : Int) : Prop :=
  ∃ (e : Int) (o : Int),
    lst.find? isEven = some e ∧
    lst.find? isOdd = some o ∧
    result = e * o

end Specs

section Impl

method findProduct (lst : List Int) return (result : Int)
  require precondition lst
  ensures postcondition lst result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: example from prompt
def test1_lst : List Int := [2, 3, 4, 5]
def test1_Expected : Int := 6

-- Test case 2: first even early, first odd appears later
def test2_lst : List Int := [2, 4, 3, 6]
def test2_Expected : Int := 6

-- Test case 3: first odd occurs before first even
def test3_lst : List Int := [1, 2, 5, 4]
def test3_Expected : Int := 2

-- Test case 4: negatives included
def test4_lst : List Int := [-3, -2, 6, 5]
def test4_Expected : Int := 6

-- Test case 5: zero as first even
def test5_lst : List Int := [0, 7, 2, 9]
def test5_Expected : Int := 0

-- Test case 6: first odd is negative
def test6_lst : List Int := [4, -5, 8, 3]
def test6_Expected : Int := -20

-- Test case 7: single even and single odd, minimal length satisfying precondition
def test7_lst : List Int := [2, 1]
def test7_Expected : Int := 2

-- Test case 8: duplicates; first occurrences matter
def test8_lst : List Int := [6, 6, 9, 9]
def test8_Expected : Int := 54

-- Test case 9: odd first, even later, with more elements
def test9_lst : List Int := [5, 7, 8, 10, 11]
def test9_Expected : Int := 40

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 3, 6

end TestCases
