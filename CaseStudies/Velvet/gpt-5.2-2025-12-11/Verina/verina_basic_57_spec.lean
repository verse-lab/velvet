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
    CountLessThan: count how many numbers in an integer array are strictly less than a given threshold.
    Natural language breakdown:
    1. Input is an array of integers `numbers` and an integer `threshold`.
    2. An element contributes to the count exactly when it is strictly less than `threshold`.
    3. The output is a natural number equal to the number of indices `i` within bounds such that `numbers[i]! < threshold`.
    4. The function must work for any array (including empty) and any integer threshold.
    5. The result is uniquely determined by the set of in-bounds indices satisfying the predicate.
-/

section Specs

-- Helper: count of elements satisfying a boolean predicate, using List.countP on the array's list view.
-- This is a mathematical characterization of the desired count.
-- (Using Mathlib/Std's List.countP and Array.toList.)
def countLessThanSpec (numbers : Array Int) (threshold : Int) : Nat :=
  (numbers.toList.countP (fun x => x < threshold))

-- No preconditions.
def precondition (numbers : Array Int) (threshold : Int) : Prop :=
  True

-- Postcondition: result equals the number of elements strictly less than threshold.
-- This is expressed as a count over the list view of the array.
def postcondition (numbers : Array Int) (threshold : Int) (result : Nat) : Prop :=
  result = countLessThanSpec numbers threshold

end Specs

section Impl

method CountLessThan (numbers : Array Int) (threshold : Int)
  return (result : Nat)
  require precondition numbers threshold
  ensures postcondition numbers threshold result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: example from prompt
-- numbers = #[1,2,3,4,5], threshold = 3 => 1 and 2 are less than 3

def test1_numbers : Array Int := #[1, 2, 3, 4, 5]
def test1_threshold : Int := 3
def test1_Expected : Nat := 2

-- Test case 2: empty array

def test2_numbers : Array Int := #[]
def test2_threshold : Int := 10
def test2_Expected : Nat := 0

-- Test case 3: mix with negatives; threshold = 0

def test3_numbers : Array Int := #[-1, 0, 1]
def test3_threshold : Int := 0
def test3_Expected : Nat := 1

-- Test case 4: unsorted array; count elements less than 5

def test4_numbers : Array Int := #[5, 6, 7, 2, 1]
def test4_threshold : Int := 5
def test4_Expected : Nat := 2

-- Test case 5: all equal to threshold (strictly less gives 0)

def test5_numbers : Array Int := #[3, 3, 3, 3]
def test5_threshold : Int := 3
def test5_Expected : Nat := 0

-- Test case 6: threshold very large; all elements counted

def test6_numbers : Array Int := #[-2, 0, 5]
def test6_threshold : Int := 100

def test6_Expected : Nat := 3

-- Test case 7: threshold very small; none counted

def test7_numbers : Array Int := #[-10, 0, 10]
def test7_threshold : Int := (-11)
def test7_Expected : Nat := 0

-- Test case 8: single element less than threshold

def test8_numbers : Array Int := #[42]
def test8_threshold : Int := 100
def test8_Expected : Nat := 1

-- Test case 9: single element equal to threshold (strictly less => 0)

def test9_numbers : Array Int := #[7]
def test9_threshold : Int := 7
def test9_Expected : Nat := 0

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 3, 4

end TestCases
