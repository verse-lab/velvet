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
    findFirstOdd: locate the first odd integer in an array.
    Natural language breakdown:
    1. Input is an array `a : Array Int`.
    2. We search indices from left to right.
    3. If there exists an index `i` with `i < a.size` and `a[i]!` is odd, we return `some i`.
    4. The returned index must be the smallest (first) index where an odd element occurs.
    5. If no odd element exists in the array, we return `none`.
    6. Arrays are assumed non-null by the language runtime.
    7. For this task, empty arrays are rejected inputs (precondition requires `a.size > 0`).
-/

section Specs

-- Helper: define oddness for integers via modulo.
-- An integer is odd iff it is not divisible by 2.

def isOdd (x : Int) : Prop := x % 2 ≠ 0

def IsOddAt (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧ isOdd (a[i]!)

-- `IsFirstOddIndex a i` means `i` is a valid index, `a[i]!` is odd,
-- and there is no earlier index with an odd element.

def IsFirstOddIndex (a : Array Int) (i : Nat) : Prop :=
  (i < a.size) ∧ isOdd (a[i]!) ∧ ∀ j : Nat, j < i → ¬ isOdd (a[j]!)

-- We reject empty arrays as specified in REJECT_INPUTS.

def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition:
-- - If result = none, then no element in the array is odd.
-- - If result = some i, then i is the first index whose element is odd.

def postcondition (a : Array Int) (result : Option Nat) : Prop :=
  match result with
  | none =>
      ∀ i : Nat, i < a.size → ¬ isOdd (a[i]!)
  | some i =>
      IsFirstOddIndex a i

end Specs

section Impl

method findFirstOdd (a : Array Int)
  return (result : Option Nat)
  require precondition a
  ensures postcondition a result
  do
    pure none  -- placeholder body

end Impl

section TestCases

-- Test case 1 (from prompt): all even -> none
-- Most important example: validates the "none" branch.
def test1_a : Array Int := #[2, 4, 6, 8]
def test1_Expected : Option Nat := none

-- Test case 2 (from prompt): first element odd -> some 0
-- Most important example: validates smallest index = 0.
def test2_a : Array Int := #[3, 4, 6, 8]
def test2_Expected : Option Nat := some 0

-- Test case 3 (from prompt): odd in middle -> some 2
-- Most important example: validates minimality (earlier evens).
def test3_a : Array Int := #[2, 4, 5, 8]
def test3_Expected : Option Nat := some 2

-- Test case 4 (from prompt): singleton odd

def test4_a : Array Int := #[7]
def test4_Expected : Option Nat := some 0

-- Test case 5 (from prompt): singleton even

def test5_a : Array Int := #[2]
def test5_Expected : Option Nat := none

-- Test case 6 (from prompt): multiple odds, first at 0

def test6_a : Array Int := #[1, 2, 3]
def test6_Expected : Option Nat := some 0

-- Test case 7: first odd appears later among negatives and evens

def test7_a : Array Int := #[-2, -4, -5, 10]
def test7_Expected : Option Nat := some 2

-- Test case 8: includes zero and a negative odd later

def test8_a : Array Int := #[0, 2, 4, -3]
def test8_Expected : Option Nat := some 3

-- Test case 9: longer, multiple odds; first is not last

def test9_a : Array Int := #[6, 8, 10, 11, 13]
def test9_Expected : Option Nat := some 3

-- Recommend to validate: 1, 2, 3

end TestCases
