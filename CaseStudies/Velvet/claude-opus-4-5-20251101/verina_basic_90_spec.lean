import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem Description
-- SlopeSearch: Search for a key in a 2D array where rows and columns are sorted in non-decreasing order
--
-- Natural language breakdown:
-- 1. We have a 2D array (Array (Array Int)) where each row is sorted in non-decreasing order
-- 2. Additionally, each column is sorted in non-decreasing order
-- 3. The goal is to find the position (row, col) of a given key in the array
-- 4. If the key is found, return the (row, col) indices where a[row][col] = key
-- 5. If the key is not found, return (-1, -1) as a sentinel value
-- 6. Preconditions:
--    a. The outer array must be non-empty (at least one row)
--    b. Each row must have the same non-zero length (rectangular matrix)
--    c. Rows are sorted in non-decreasing order
--    d. Columns are sorted in non-decreasing order
-- 7. Postconditions:
--    a. If result is (row, col) with row >= 0 and col >= 0:
--       - row and col must be valid indices
--       - a[row][col] must equal the key
--    b. If result is (-1, -1):
--       - The key does not exist anywhere in the array
-- 8. This is the classic "staircase search" or "saddleback search" problem

section Specs

-- Helper function to access 2D array element
def get2d (a : Array (Array Int)) (row : Nat) (col : Nat) : Int :=
  let rowArr := a[row]!
  rowArr[col]!

-- Helper: check if all rows have the same length
def allRowsSameLength (a : Array (Array Int)) : Prop :=
  ∀ i : Nat, i < a.size → a[i]!.size = a[0]!.size

-- Helper: check if all rows are non-empty
def allRowsNonEmpty (a : Array (Array Int)) : Prop :=
  a[0]!.size > 0

-- Helper: check if a single row is sorted in non-decreasing order
def rowSorted (row : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < row.size → row[i]! ≤ row[j]!

-- Helper: check if all rows are sorted
def allRowsSorted (a : Array (Array Int)) : Prop :=
  ∀ i : Nat, i < a.size → rowSorted a[i]!

-- Helper: check if columns are sorted in non-decreasing order
def columnsSorted (a : Array (Array Int)) : Prop :=
  ∀ col : Nat, col < a[0]!.size →
    ∀ i j : Nat, i < j → j < a.size → get2d a i col ≤ get2d a j col

-- Helper: check if key exists in the array
def keyExists (a : Array (Array Int)) (key : Int) : Prop :=
  ∃ row col : Nat, row < a.size ∧ col < a[0]!.size ∧ get2d a row col = key

-- Precondition: valid sorted 2D array
def precondition (a : Array (Array Int)) (key : Int) : Prop :=
  a.size > 0 ∧
  allRowsNonEmpty a ∧
  allRowsSameLength a ∧
  allRowsSorted a ∧
  columnsSorted a

-- Postcondition: result is valid position of key or (-1, -1) if not found
def postcondition (a : Array (Array Int)) (key : Int) (result : Int × Int) : Prop :=
  let (row, col) := result
  (row ≥ 0 ∧ col ≥ 0 →
    row.toNat < a.size ∧
    col.toNat < a[0]!.size ∧
    get2d a row.toNat col.toNat = key) ∧
  (row = -1 ∧ col = -1 →
    ¬keyExists a key) ∧
  ((row ≥ 0 ∧ col ≥ 0) ∨ (row = -1 ∧ col = -1))

end Specs

section Impl

method SlopeSearch (a : Array (Array Int)) (key : Int)
  return (result : Int × Int)
  require precondition a key
  ensures postcondition a key result
  do
    pure (-1, -1)

end Impl

section TestCases

-- Test case 1: Key found in the middle (example from problem)
def test1_a : Array (Array Int) := #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]
def test1_key : Int := 5
def test1_Expected : Int × Int := (1, 1)

-- Test case 2: Key found at corner (top-right)
def test2_a : Array (Array Int) := #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]
def test2_key : Int := 3
def test2_Expected : Int × Int := (0, 2)

-- Test case 3: Key not found in the array
def test3_a : Array (Array Int) := #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]
def test3_key : Int := 10
def test3_Expected : Int × Int := (-1, -1)

-- Test case 4: Single row array, key found at end
def test4_a : Array (Array Int) := #[#[1, 2, 3, 4]]
def test4_key : Int := 4
def test4_Expected : Int × Int := (0, 3)

-- Test case 5: Single column array, key found
def test5_a : Array (Array Int) := #[#[1], #[2], #[3], #[4]]
def test5_key : Int := 3
def test5_Expected : Int × Int := (2, 0)

-- Test case 6: Key found at top-left corner
def test6_a : Array (Array Int) := #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]
def test6_key : Int := 1
def test6_Expected : Int × Int := (0, 0)

-- Test case 7: Key found at bottom-right corner
def test7_a : Array (Array Int) := #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]
def test7_key : Int := 9
def test7_Expected : Int × Int := (2, 2)

-- Test case 8: Single element array, key found
def test8_a : Array (Array Int) := #[#[42]]
def test8_key : Int := 42
def test8_Expected : Int × Int := (0, 0)

-- Test case 9: Single element array, key not found
def test9_a : Array (Array Int) := #[#[42]]
def test9_key : Int := 100
def test9_Expected : Int × Int := (-1, -1)

-- Test case 10: Key not in array (less than minimum)
def test10_a : Array (Array Int) := #[#[5, 10, 15], #[20, 25, 30]]
def test10_key : Int := 0
def test10_Expected : Int × Int := (-1, -1)

-- Recommend to validate: 1, 3, 5

end TestCases
