import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    minOperations: Find minimum number of removal operations to collect integers 1 to k
    
    Natural language breakdown:
    1. We have a list of positive integers nums and a target k
    2. A removal operation removes the last element from nums and adds it to our collection
    3. We want to collect all integers from 1 to k (inclusive)
    4. We need to find the minimum number of removal operations required
    5. The result is the smallest index i (counting from the end) such that 
       the suffix nums[n-i..n-1] contains all integers from 1 to k
    6. Elements greater than k in the suffix are ignored (they don't contribute to the collection)
    7. If k = 0, we need to collect nothing, so result is 0
    8. The precondition guarantees that nums contains all integers from 1 to k
-/

section Specs

-- Helper: Check if all integers from 1 to k are present in a list
def containsAllUpToK (collected : List Nat) (k : Nat) : Prop :=
  ∀ i : Nat, 1 ≤ i ∧ i ≤ k → i ∈ collected

-- Helper: Get the suffix of length n from a list (last n elements)
def listSuffix (l : List Nat) (n : Nat) : List Nat :=
  l.drop (l.length - n)

-- Precondition: nums contains all integers from 1 to k
def require1 (nums : List Nat) (k : Nat) :=
  containsAllUpToK nums k

def precondition (nums : List Nat) (k : Nat) :=
  require1 nums k

-- Postcondition clauses
-- The result is at most the length of the list
def ensures1 (nums : List Nat) (k : Nat) (result : Nat) :=
  result ≤ nums.length

-- The suffix of length result contains all integers from 1 to k
def ensures2 (nums : List Nat) (k : Nat) (result : Nat) :=
  containsAllUpToK (listSuffix nums result) k

-- The result is minimal: no smaller suffix contains all integers from 1 to k
def ensures3 (nums : List Nat) (k : Nat) (result : Nat) :=
  ∀ m : Nat, m < result → ¬containsAllUpToK (listSuffix nums m) k

def postcondition (nums : List Nat) (k : Nat) (result : Nat) :=
  ensures1 nums k result ∧
  ensures2 nums k result ∧
  ensures3 nums k result

end Specs

section Impl

method minOperations (nums : List Nat) (k : Nat)
  return (result : Nat)
  require precondition nums k
  ensures postcondition nums k result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: Example from problem - collect 1 and 2 from [3, 1, 5, 4, 2]
-- Remove from end: 2, 4, 5, 1 -> after 4 removals we have {2, 4, 5, 1} which contains 1 and 2
def test1_nums : List Nat := [3, 1, 5, 4, 2]
def test1_k : Nat := 2
def test1_Expected : Nat := 4

-- Test case 2: Collect all 1 to 5 from [3, 1, 5, 4, 2]
-- Need to remove all 5 elements to get 1, 2, 3, 4, 5
def test2_nums : List Nat := [3, 1, 5, 4, 2]
def test2_k : Nat := 5
def test2_Expected : Nat := 5

-- Test case 3: List with duplicates [3, 2, 5, 3, 1], k = 3
-- Remove: 1, 3, 5, 2 -> after 4 removals we have {1, 3, 5, 2} which contains 1, 2, 3
def test3_nums : List Nat := [3, 2, 5, 3, 1]
def test3_k : Nat := 3
def test3_Expected : Nat := 4

-- Test case 4: Target at end [5, 4, 3, 2, 1], k = 1
-- Remove: 1 -> after 1 removal we have {1} which contains 1
def test4_nums : List Nat := [5, 4, 3, 2, 1]
def test4_k : Nat := 1
def test4_Expected : Nat := 1

-- Test case 5: Targets near end [5, 4, 1, 2, 3], k = 3
-- Remove: 3, 2, 1 -> after 3 removals we have {3, 2, 1} which contains 1, 2, 3
def test5_nums : List Nat := [5, 4, 1, 2, 3]
def test5_k : Nat := 3
def test5_Expected : Nat := 3

-- Test case 6: List with duplicates [1, 3, 2, 2, 1], k = 2
-- Remove: 1, 2 -> after 2 removals we have {1, 2} which contains 1 and 2
def test6_nums : List Nat := [1, 3, 2, 2, 1]
def test6_k : Nat := 2
def test6_Expected : Nat := 2

-- Test case 7: Sparse list [10, 1, 20, 2], k = 2
-- Remove: 2, 20, 1 -> after 3 removals we have {2, 20, 1} which contains 1 and 2
def test7_nums : List Nat := [10, 1, 20, 2]
def test7_k : Nat := 2
def test7_Expected : Nat := 3

-- Test case 8: Edge case k = 0 (need to collect nothing)
def test8_nums : List Nat := [1, 2, 3]
def test8_k : Nat := 0
def test8_Expected : Nat := 0

-- Recommend to validate: 1, 4, 8

end TestCases
