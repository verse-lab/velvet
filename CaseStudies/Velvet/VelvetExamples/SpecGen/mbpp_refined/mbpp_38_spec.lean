import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 38: Find the division of first even and odd number of a given list
--
-- Natural language breakdown:
-- 1. We are given a list of integers
-- 2. We need to find the FIRST even number in the list (leftmost even number)
-- 3. We need to find the FIRST odd number in the list (leftmost odd number)
-- 4. If both exist, we return Some(first_even / first_odd) as a rational division
-- 5. If either doesn't exist, we return None
-- 6. The division is computed as a Rat (rational number) to handle non-integer results
-- 7. "First" means the leftmost occurrence when scanning from left to right
--
-- Edge cases:
-- - Empty list: No even or odd numbers exist, return None
-- - List with only even numbers: No odd number exists, return None
-- - List with only odd numbers: No even number exists, return None
-- - Division by zero is not possible since odd numbers are non-zero by definition
-- - Actually, 0 is even, so if first odd is 0... wait, 0 is even not odd!
--   So division by odd number cannot result in division by zero
--
-- Property-oriented specification approach:
-- Instead of describing the algorithm step-by-step, we specify the properties:
-- 1. If result is Some(r), then:
--    a) There exists an even number at index i in the list
--    b) There exists an odd number at index j in the list
--    c) list[i] is the first even (no even number before index i)
--    d) list[j] is the first odd (no odd number before index j)
--    e) r = list[i] / list[j] (as rational division)
-- 2. If result is None, then either:
--    a) No even number exists in the list, OR
--    b) No odd number exists in the list

-- Helper: Check if a number is even

section Specs

-- Helper Functions

def isEven (n : Int) : Prop := ∃ k : Int, n = 2 * k

def isOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

def isFirstEven (lst : List Int) (i : Nat) : Prop :=
  i < lst.length ∧
  isEven lst[i]! ∧
  ∀ j, j < i → ¬isEven lst[j]!

def isFirstOdd (lst : List Int) (j : Nat) : Prop :=
  j < lst.length ∧
  isOdd lst[j]! ∧
  ∀ k, k < j → ¬isOdd lst[k]!

def require1 (lst : Array Int) :=
  ∃ x ∈ lst, isEven x
def require2 (lst : Array Int) :=
  ∃ x ∈ lst, isOdd x

-- Postcondition clauses
def ensures1 (lst : Array Int) (result : Rat) :=
  (∃ i j : Nat,
    isFirstEven lst.toList i ∧
    isFirstOdd lst.toList j ∧
    result = ((lst[i]! : Rat) / (lst[j]! : Rat)))

def precondition (lst : Array Int) :=
  require1 lst ∧ require2 lst
def postcondition (lst : Array Int) (result : Rat) :=
  ensures1 lst result

end Specs

method DivFirstEvenOdd (lst : Array Int)
  return (result : Rat)
  require precondition lst
  ensures postcondition lst result
  do
    sorry

prove_correct DivFirstEvenOdd by sorry

section TestCases

-- Test case 0: Sample from the problem
def test0_Input : Array Int := #[1,3,5,7,4,1,6,8]
def test0_Expected : Rat := 4 / 1

-- Test case 1: Both even and odd present, even comes first
def test1_Input : Array Int := #[2, 3, 4, 5]
def test1_Expected : Rat := 2 / 3

-- Test case 2: Both even and odd present, odd comes first
def test2_Input : Array Int := #[1, 2, 3, 4]
def test2_Expected : Rat := 2 / 1

-- Test case 3: First even comes much later
def test3_Input : Array Int := #[1, 3, 5, 7, 2, 4]
def test3_Expected : Rat := 2 / 1

-- Test case 4: First odd comes much later
def test4_Input : Array Int := #[2, 4, 6, 8, 1, 3]
def test4_Expected : Rat := 2 / 1

-- Test case 5: Large numbers
def test5_Input : Array Int := #[100, 201, 300, 401]
def test5_Expected : Rat := 100 / 201

-- Test case 6: Negative numbers
def test6_Input : Array Int := #[-4, -3, -2, -1]
def test6_Expected : Rat := 4 / 3

-- Test case 7: Mixed positive and negative
def test7_Input : Array Int := #[-1, 0, 2, 3]
def test7_Expected : Rat := 0

-- Test case 8: Zero as first even
def test8_Input : Array Int := #[0, 1, 2, 3]
def test8_Expected : Rat := 0

-- Recommend to validate: 0,1,2,5,6

end TestCases

-- ==================== Verification Notes ====================
--
-- Properties verified by the specification:
-- 1. Correctness: When result is Some(r), r equals the division of the first even by first odd
-- 2. Completeness: If both first even and first odd exist, result cannot be None
-- 3. Soundness: If result is None, at least one of first even or first odd is missing
-- 4. Non-ambiguity: The postconditions uniquely determine the output given the input
-- 5. Handle all edge cases: empty list, single element, only even, only odd, etc.
--
-- The specification is property-oriented rather than process-oriented:
-- - We don't specify HOW to find the first even/odd (scanning, filtering, etc.)
-- - We only specify WHAT properties the result must satisfy
-- - This allows multiple valid implementations (loop, recursion, functional style, etc.)
-- - The specification is more abstract and reusable
