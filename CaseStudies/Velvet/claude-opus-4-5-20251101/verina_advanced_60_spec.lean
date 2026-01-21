import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    partitionEvensOdds: Partition a list of natural numbers into even and odd sublists
    Natural language breakdown:
    1. We have an input list of natural numbers with no duplicates
    2. We need to partition this list into two separate lists
    3. The first output list contains all even numbers from the input
    4. The second output list contains all odd numbers from the input
    5. A natural number n is even if n % 2 = 0
    6. A natural number n is odd if n % 2 ≠ 0 (equivalently n % 2 = 1)
    7. The order of elements in each sublist must match their appearance in the original list
    8. Every element from the input must appear in exactly one of the output lists
    9. The union of both output lists equals the input list (in terms of elements)
    10. Empty input should produce two empty lists
-/

section Specs

-- Predicate: a natural number is even
def isEven (n : Nat) : Bool := n % 2 = 0

-- Predicate: a natural number is odd
def isOdd (n : Nat) : Bool := n % 2 ≠ 0

-- Postcondition: result.1 contains exactly the even numbers from nums in order
-- and result.2 contains exactly the odd numbers from nums in order
def ensures1 (nums : List Nat) (result : List Nat × List Nat) :=
  result.1.Sublist nums ∧ result.2.Sublist nums

-- All elements in first list are even, all in second are odd
def ensures2 (nums : List Nat) (result : List Nat × List Nat) :=
  (∀ x ∈ result.1, x % 2 = 0) ∧ (∀ x ∈ result.2, x % 2 ≠ 0)

-- Every even element from nums is in result.1, every odd element is in result.2
def ensures3 (nums : List Nat) (result : List Nat × List Nat) :=
  (∀ x ∈ nums, x % 2 = 0 → x ∈ result.1) ∧
  (∀ x ∈ nums, x % 2 ≠ 0 → x ∈ result.2)

-- Counts are preserved
def ensures4 (nums : List Nat) (result : List Nat × List Nat) :=
  (∀ x, x % 2 = 0 → result.1.count x = nums.count x) ∧
  (∀ x, x % 2 ≠ 0 → result.2.count x = nums.count x)

def precondition (nums : List Nat) :=
  nums.Nodup  -- no duplicates in input

def postcondition (nums : List Nat) (result : List Nat × List Nat) :=
  ensures1 nums result ∧ ensures2 nums result ∧ ensures3 nums result ∧ ensures4 nums result

end Specs

section Impl

method partitionEvensOdds (nums : List Nat)
  return (result : List Nat × List Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure ([], [])  -- placeholder

end Impl

section TestCases

-- Test case 1: Mixed list from problem description
def test1_nums : List Nat := [1, 2, 3, 4, 5, 6]
def test1_Expected : List Nat × List Nat := ([2, 4, 6], [1, 3, 5])

-- Test case 2: List starting with zero
def test2_nums : List Nat := [0, 7, 8, 9, 10]
def test2_Expected : List Nat × List Nat := ([0, 8, 10], [7, 9])

-- Test case 3: Empty list
def test3_nums : List Nat := []
def test3_Expected : List Nat × List Nat := ([], [])

-- Test case 4: All even numbers
def test4_nums : List Nat := [2, 4, 6, 8]
def test4_Expected : List Nat × List Nat := ([2, 4, 6, 8], [])

-- Test case 5: All odd numbers
def test5_nums : List Nat := [1, 3, 5, 7]
def test5_Expected : List Nat × List Nat := ([], [1, 3, 5, 7])

-- Test case 6: Single even element
def test6_nums : List Nat := [42]
def test6_Expected : List Nat × List Nat := ([42], [])

-- Test case 7: Single odd element
def test7_nums : List Nat := [37]
def test7_Expected : List Nat × List Nat := ([], [37])

-- Test case 8: Alternating even and odd
def test8_nums : List Nat := [2, 1, 4, 3, 6, 5]
def test8_Expected : List Nat × List Nat := ([2, 4, 6], [1, 3, 5])

-- Test case 9: Large numbers
def test9_nums : List Nat := [100, 101, 200, 201]
def test9_Expected : List Nat × List Nat := ([100, 200], [101, 201])

-- Test case 10: Zero only
def test10_nums : List Nat := [0]
def test10_Expected : List Nat × List Nat := ([0], [])

-- Recommend to validate: 1, 3, 4

end TestCases

