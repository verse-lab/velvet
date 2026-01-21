import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findProduct: Compute the product of the first even and first odd number in a list
    
    Natural language breakdown:
    1. We are given a list of integers
    2. We need to find the first (leftmost) even number in the list
    3. We need to find the first (leftmost) odd number in the list
    4. We compute and return the product of these two numbers
    5. The list is guaranteed to contain at least one even number and at least one odd number
    
    Property-oriented specification:
    - The result is the product of two specific elements from the list
    - One element is the first even number (no even number appears before it)
    - One element is the first odd number (no odd number appears before it)
    - These elements exist by precondition
-/

section Specs

-- Helper Functions

-- Check if an integer is even
def isEven (n : Int) : Prop := n % 2 = 0

-- Check if an integer is odd
def isOdd (n : Int) : Prop := n % 2 ≠ 0

-- Predicate: element at index i is the first even number in the list
def isFirstEvenAt (lst : List Int) (i : Nat) : Prop :=
  i < lst.length ∧
  isEven lst[i]! ∧
  ∀ j : Nat, j < i → ¬isEven lst[j]!

-- Predicate: element at index i is the first odd number in the list
def isFirstOddAt (lst : List Int) (i : Nat) : Prop :=
  i < lst.length ∧
  isOdd lst[i]! ∧
  ∀ j : Nat, j < i → ¬isOdd lst[j]!

-- Precondition: list contains at least one even and at least one odd number
def require1 (lst : List Int) : Prop :=
  ∃ x ∈ lst, isEven x

def require2 (lst : List Int) : Prop :=
  ∃ x ∈ lst, isOdd x

-- Postcondition: result is product of first even and first odd
def ensures1 (lst : List Int) (result : Int) : Prop :=
  ∃ i j : Nat,
    isFirstEvenAt lst i ∧
    isFirstOddAt lst j ∧
    result = lst[i]! * lst[j]!

def precondition (lst : List Int) : Prop :=
  require1 lst ∧ require2 lst

def postcondition (lst : List Int) (result : Int) : Prop :=
  ensures1 lst result

end Specs

section Impl

method findProduct (lst : List Int)
  return (result : Int)
  require precondition lst
  ensures postcondition lst result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - [2, 3, 4, 5], first even = 2, first odd = 3, product = 6
def test1_lst : List Int := [2, 3, 4, 5]
def test1_Expected : Int := 6

-- Test case 2: [2, 4, 3, 6], first even = 2, first odd = 3, product = 6
def test2_lst : List Int := [2, 4, 3, 6]
def test2_Expected : Int := 6

-- Test case 3: [1, 2, 5, 4], first even = 2, first odd = 1, product = 2
def test3_lst : List Int := [1, 2, 5, 4]
def test3_Expected : Int := 2

-- Test case 4: Odd comes first - [3, 2], first even = 2, first odd = 3, product = 6
def test4_lst : List Int := [3, 2]
def test4_Expected : Int := 6

-- Test case 5: Even comes first - [4, 5], first even = 4, first odd = 5, product = 20
def test5_lst : List Int := [4, 5]
def test5_Expected : Int := 20

-- Test case 6: Negative numbers - [-2, -3, 4, 5], first even = -2, first odd = -3, product = 6
def test6_lst : List Int := [-2, -3, 4, 5]
def test6_Expected : Int := 6

-- Test case 7: Zero as first even - [0, 1, 2, 3], first even = 0, first odd = 1, product = 0
def test7_lst : List Int := [0, 1, 2, 3]
def test7_Expected : Int := 0

-- Test case 8: Mixed with multiple evens and odds - [7, 9, 4, 2, 3], first even = 4, first odd = 7, product = 28
def test8_lst : List Int := [7, 9, 4, 2, 3]
def test8_Expected : Int := 28

-- Test case 9: Negative product - [-4, 3, 2, 5], first even = -4, first odd = 3, product = -12
def test9_lst : List Int := [-4, 3, 2, 5]
def test9_Expected : Int := -12

-- Test case 10: Large numbers - [100, 101], first even = 100, first odd = 101, product = 10100
def test10_lst : List Int := [100, 101]
def test10_Expected : Int := 10100

-- Recommend to validate: 1, 3, 7

end TestCases
