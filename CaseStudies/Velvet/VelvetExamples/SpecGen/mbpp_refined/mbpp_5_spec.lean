import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    DominoTiling: Find the number of ways to fill a 3×n board with 2×1 dominoes
    Natural language breakdown:
    1. We have a rectangular board with exactly 3 rows and n columns (3×n board)
    2. We want to completely fill this board using 2×1 dominoes (rectangular pieces covering exactly 2 adjacent squares)
    3. Dominoes can be placed either horizontally or vertically
    4. The board must be completely filled with no empty squares and no overlapping dominoes
    5. We count the number of distinct ways to achieve such a complete tiling
    6. Key insight: A 3×n board has 3n total squares
    7. Each 2×1 domino covers exactly 2 squares
    8. For a perfect tiling to exist, 3n must be divisible by 2
    9. This means n must be even (if n is odd, 3n is odd and cannot be divided by 2)
    10. Therefore, for ANY odd n, the result must be 0
    11. For even n, there exists a recurrence relation: f(n) = 4*f(n-2) - f(n-4) for n≥4
    12. Base cases: f(0) = 1 (empty board), f(2) = 3
-/

-- Helper Functions

-- The recurrence relation for domino tiling of 3×n board
-- This captures the mathematical structure of the problem

section Specs

register_specdef_allow_recursion

-- Helper Functions

def dominoTilingRecurrence (n: Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 0
  | n + 4 => 4 * dominoTilingRecurrence (n + 2) - dominoTilingRecurrence n

-- Postcondition clauses
def ensures1 (n : Nat) (count : Nat) :=
  count = dominoTilingRecurrence n  -- For even n≥4, follows recurrence relation

def precondition (n : Nat) :=
  True  -- no preconditions
def postcondition (n : Nat) (count : Nat) :=
  ensures1 n count

end Specs

section Impl

method DominoTiling (n: Nat)
  return (count: Nat)
  require precondition n
  ensures postcondition n count
  do
    sorry

prove_correct DominoTiling by sorry

end Impl

section TestCases

-- Test case 1: From problem description (MUST be first)
def test1_n : Nat := 2
def test1_Expected : Nat := 3

-- Test case 2: Empty board (edge case)
def test2_n : Nat := 0
def test2_Expected : Nat := 1

-- Test case 3: Single column (odd n = 1)
def test3_n : Nat := 1
def test3_Expected : Nat := 0

-- Test case 4: Three columns (odd n = 3)
def test4_n : Nat := 3
def test4_Expected : Nat := 0

-- Test case 5: Five columns (larger odd n = 5)
def test5_n : Nat := 5
def test5_Expected : Nat := 0

-- Test case 6: Seven columns (larger odd n = 7)
def test6_n : Nat := 7
def test6_Expected : Nat := 0

-- Test case 7: Four columns (even n = 4)
def test7_n : Nat := 4
def test7_Expected : Nat := 11

-- Test case 8: Six columns (even n = 6)
def test8_n : Nat := 6
def test8_Expected : Nat := 41

-- Test case 9: Eight columns (even n = 8)
def test9_n : Nat := 8
def test9_Expected : Nat := 153

-- Test case 10: Ten columns (even n = 10)
def test10_n : Nat := 10
def test10_Expected : Nat := 571

-- Test case 11: Nine columns (larger odd n = 9)
def test11_n : Nat := 9
def test11_Expected : Nat := 0

-- Test case 12: Eleven columns (larger odd n = 11)
def test12_n : Nat := 11
def test12_Expected : Nat := 0

-- Recommend to validate: test cases 1, 3, 5, 6, 7, 8
-- These cover:
-- - Test 1: Problem statement example (required, even n=2)
-- - Test 3: Small odd n=1
-- - Test 5: Larger odd n=5 (validates general odd constraint)
-- - Test 6: Larger odd n=7 (validates general odd constraint)
-- - Test 7: Even n=4 (recurrence relation)
-- - Test 8: Even n=6 (recurrence relation)

end TestCases
