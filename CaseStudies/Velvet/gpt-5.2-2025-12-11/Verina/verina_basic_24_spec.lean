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
    verina_basic_24: difference between first even and first odd integers in an array.
    Natural language breakdown:
    1. Input is an array `a : Array Int`.
    2. The array is assumed non-empty and contains at least one even element and at least one odd element.
    3. “First even” means the element at the smallest index `i` such that `Even (a[i]!)`.
    4. “First odd” means the element at the smallest index `j` such that `Odd (a[j]!)`.
    5. The output is an integer equal to (first even element) minus (first odd element).
    6. The result should be uniquely determined by the minimality of these indices.
-/

section Specs

-- Helper: predicate that an index is the first index satisfying a property.
-- We phrase it using Nat indices and `a[i]!` access, with explicit bounds.
def IsFirstIdx (a : Array Int) (p : Int → Prop) (i : Nat) : Prop :=
  i < a.size ∧ p (a[i]!) ∧ ∀ k : Nat, k < i → ¬ p (a[k]!)

-- Preconditions: array must contain at least one even and at least one odd element.
def precondition (a : Array Int) : Prop :=
  (∃ i : Nat, i < a.size ∧ Even (a[i]!)) ∧
  (∃ j : Nat, j < a.size ∧ Odd (a[j]!))

-- Postcondition: there exist minimal indices of first even and first odd,
-- and result is their difference.
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ i : Nat, ∃ j : Nat,
    IsFirstIdx a (fun x => Even x) i ∧
    IsFirstIdx a (fun x => Odd x) j ∧
    result = a[i]! - a[j]!

end Specs

section Impl

method firstEvenOddDifference (a : Array Int) return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: example from prompt
-- a = #[2, 3, 4, 5]; first even = 2, first odd = 3, diff = -1

def test1_a : Array Int := #[2, 3, 4, 5]
def test1_Expected : Int := -1

-- Test case 2: first odd appears before first even
-- a = #[1, 4, 6, 8]; first even = 4, first odd = 1, diff = 3

def test2_a : Array Int := #[1, 4, 6, 8]
def test2_Expected : Int := 3

-- Test case 3: odd first, then even
-- a = #[7, 2, 9, 4]; first even = 2, first odd = 7, diff = -5

def test3_a : Array Int := #[7, 2, 9, 4]
def test3_Expected : Int := -5

-- Test case 4: repeated evens then repeated odds
-- a = #[2, 2, 3, 3]; first even = 2, first odd = 3, diff = -1

def test4_a : Array Int := #[2, 2, 3, 3]
def test4_Expected : Int := -1

-- Test case 5: repeated odds then repeated evens
-- a = #[1, 1, 2, 2]; first even = 2, first odd = 1, diff = 1

def test5_a : Array Int := #[1, 1, 2, 2]
def test5_Expected : Int := 1

-- Test case 6: includes zero (even) and negative odd
-- a = #[0, -3, 2, 5]; first even = 0, first odd = -3, diff = 3

def test6_a : Array Int := #[0, -3, 2, 5]
def test6_Expected : Int := 3

-- Test case 7: negative even occurs after negative odd
-- a = #[-1, -4, 3]; first even = -4, first odd = -1, diff = -3

def test7_a : Array Int := #[-1, -4, 3]
def test7_Expected : Int := -3

-- Test case 8: first even and odd are adjacent
-- a = #[6, 5]; first even = 6, first odd = 5, diff = 1

def test8_a : Array Int := #[6, 5]
def test8_Expected : Int := 1

-- Test case 9: larger mix, first even not at index 0
-- a = #[9, 9, 8, 7, 6]; first even = 8, first odd = 9, diff = -1

def test9_a : Array Int := #[9, 9, 8, 7, 6]
def test9_Expected : Int := -1

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 2, 6

end TestCases
