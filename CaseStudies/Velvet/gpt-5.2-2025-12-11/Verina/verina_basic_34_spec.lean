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
    findEvenNumbers: Extract even numbers from an array of integers, preserving order.
    Natural language breakdown:
    1. Input is an array of integers `arr` (may be empty).
    2. Output is an array `result` containing only elements of `arr` that are even.
    3. Every element of `result` is even.
    4. Every even element occurring in `arr` appears in `result` with the same multiplicity.
    5. The relative order of the kept (even) elements is the same as in `arr`.
    6. There are no preconditions.
-/

section Specs

-- Helper predicate: integer evenness.
-- Use `decide` to produce a Bool, so we can keep simple Bool-valued constraints.
def isEvenInt (x : Int) : Bool :=
  decide (x % 2 = 0)

def precondition (arr : Array Int) : Prop :=
  True

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  let l := arr.toList
  let r := result.toList
  -- Order preservation: output is a sublist of the input list.
  r.Sublist l ∧
  -- Only evens are present.
  (∀ x, x ∈ r → isEvenInt x = true) ∧
  -- Exact multiplicity of evens; no odds are included.
  (∀ x,
      (isEvenInt x = true → r.count x = l.count x) ∧
      (isEvenInt x = false → r.count x = 0))

end Specs

section Impl

method findEvenNumbers (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure (#[] : Array Int)  -- placeholder

end Impl

section TestCases

-- Test case 1: example from prompt
-- Input: #[1,2,3,4,5,6] => #[2,4,6]
def test1_arr : Array Int := #[1, 2, 3, 4, 5, 6]
def test1_Expected : Array Int := #[2, 4, 6]

-- Test case 2: mixture with gaps
-- #[7,8,10,13,14] => #[8,10,14]
def test2_arr : Array Int := #[7, 8, 10, 13, 14]
def test2_Expected : Array Int := #[8, 10, 14]

-- Test case 3: all odd => empty
-- #[1,3,5,7] => #[]
def test3_arr : Array Int := #[1, 3, 5, 7]
def test3_Expected : Array Int := #[]

-- Test case 4: empty input => empty output
-- #[] => #[]
def test4_arr : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: includes 0 and negative evens
-- #[0,-2,-3,-4,5] => #[0,-2,-4]
def test5_arr : Array Int := #[0, -2, -3, -4, 5]
def test5_Expected : Array Int := #[0, -2, -4]

-- Test case 6: repeated evens and odds; multiplicity preserved
-- #[2,2,3,2,4,4,5] => #[2,2,2,4,4]
def test6_arr : Array Int := #[2, 2, 3, 2, 4, 4, 5]
def test6_Expected : Array Int := #[2, 2, 2, 4, 4]

-- Test case 7: single element even
-- #[-6] => #[-6]
def test7_arr : Array Int := #[-6]
def test7_Expected : Array Int := #[-6]

-- Test case 8: single element odd
-- #[9] => #[]
def test8_arr : Array Int := #[9]
def test8_Expected : Array Int := #[]

-- Test case 9: alternating parity, preserve relative order
-- #[2,1,4,3,6,5] => #[2,4,6]
def test9_arr : Array Int := #[2, 1, 4, 3, 6, 5]
def test9_Expected : Array Int := #[2, 4, 6]

-- Recommend to validate: test1, test5, test6

end TestCases
