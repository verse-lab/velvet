import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    minimumRightShifts: Calculate the minimum number of right shifts to sort a list

    Natural language breakdown:
    1. A right shift moves the last element to the front, shifting all others right by one position
    2. Equivalently, a right shift is a left rotation by (n-1) positions, or the inverse of a left rotation
    3. For a list of length n, performing k right shifts is equivalent to rotating left by (n-k) mod n positions
    4. A list can be sorted by right shifts if and only if it is a rotation of a sorted list
    5. A rotated sorted list has at most one "descent" - a position where an element is greater than the next
    6. If the list is already sorted, return 0
    7. If the list has more than one descent, it cannot be sorted by rotations, return -1
    8. If there is exactly one descent at position i (nums[i] > nums[i+1]), then:
       - The minimum element is at position i+1
       - We need (n - (i+1)) = (n - i - 1) right shifts to bring it to the front
    9. After the right shifts, we must verify the list would actually be sorted
    10. All elements are distinct positive integers (precondition)
-/

section Specs

-- Helper: perform k right shifts on a list
-- A right shift moves last element to front: [a,b,c,d] -> [d,a,b,c]
-- k right shifts on list of length n is equivalent to List.rotate l (n - k % n) mod n
def rightShift (l : List Int) (k : Nat) : List Int :=
  if l.length = 0 then l
  else
    let effectiveK := k % l.length
    if effectiveK = 0 then l
    else l.rotate (l.length - effectiveK)

-- Helper: check if list is sorted in strictly ascending order
def isStrictlySorted (l : List Int) : Prop :=
  ∀ i : Nat, i + 1 < l.length → l[i]! < l[i + 1]!

-- Helper: check if all elements are distinct
def allDistinct (l : List Int) : Prop :=
  l.Nodup

-- Helper: check if all elements are positive
def allPositive (l : List Int) : Prop :=
  ∀ i : Nat, i < l.length → l[i]! > 0

-- Preconditions
def require1 (nums : List Int) := nums.length > 0
def require2 (nums : List Int) := allDistinct nums
def require3 (nums : List Int) := allPositive nums

def precondition (nums : List Int) :=
  require1 nums ∧ require2 nums ∧ require3 nums

-- Postcondition clauses
-- If result >= 0, then performing result right shifts produces a sorted list
def ensures1 (nums : List Int) (result : Int) :=
  result ≥ 0 → isStrictlySorted (rightShift nums result.toNat)

-- If result >= 0, the result is minimal (no smaller number of shifts works)
def ensures2 (nums : List Int) (result : Int) :=
  result ≥ 0 → ∀ k : Nat, k < result.toNat → ¬isStrictlySorted (rightShift nums k)

-- If result = -1, no number of right shifts can sort the list
-- Since rotations are periodic with period nums.length, we check all possible rotations
def ensures3 (nums : List Int) (result : Int) :=
  result = -1 → ∀ k : Nat, ¬isStrictlySorted (rightShift nums k)

-- Result is either -1 or a valid shift count (0 to n-1)
def ensures4 (nums : List Int) (result : Int) :=
  result = -1 ∨ (result ≥ 0 ∧ result < nums.length)

def postcondition (nums : List Int) (result : Int) :=
  ensures1 nums result ∧
  ensures2 nums result ∧
  ensures3 nums result ∧
  ensures4 nums result

end Specs

section Impl

method minimumRightShifts (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases

-- Test case 1: [3, 4, 5, 1, 2] - rotated sorted list, needs 2 right shifts
def test1_nums : List Int := [3, 4, 5, 1, 2]
def test1_Expected : Int := 2

-- Test case 2: [1, 3, 5] - already sorted
def test2_nums : List Int := [1, 3, 5]
def test2_Expected : Int := 0

-- Test case 3: [2, 1, 4] - cannot be sorted by right shifts
def test3_nums : List Int := [2, 1, 4]
def test3_Expected : Int := -1

-- Test case 4: [1] - single element, already sorted
def test4_nums : List Int := [1]
def test4_Expected : Int := 0

-- Test case 5: [2, 1] - two elements, needs 1 right shift
def test5_nums : List Int := [2, 1]
def test5_Expected : Int := 1

-- Test case 6: [1, 2, 3, 4, 5] - already sorted
def test6_nums : List Int := [1, 2, 3, 4, 5]
def test6_Expected : Int := 0

-- Test case 7: [5, 1, 2, 3, 4] - minimum at position 1, needs 4 right shifts
def test7_nums : List Int := [5, 1, 2, 3, 4]
def test7_Expected : Int := 4

-- Test case 8: [1, 5, 2, 3, 4] - cannot be sorted by right shifts (multiple descents)
def test8_nums : List Int := [1, 5, 2, 3, 4]
def test8_Expected : Int := -1

-- Recommend to validate: 1, 3, 5

end TestCases
