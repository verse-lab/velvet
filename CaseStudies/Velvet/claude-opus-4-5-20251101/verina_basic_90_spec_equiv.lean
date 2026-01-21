import Lean
import Mathlib.Tactic

namespace VerinaSpec

@[reducible, simp]
def get2d (a : Array (Array Int)) (i j : Int) : Int :=
  (a[Int.toNat i]!)[Int.toNat j]!

def SlopeSearch_precond (a : Array (Array Int)) (key : Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧
  (a[0]!).size > 0 ∧  -- non-empty inner arrays
  List.Pairwise (·.size = ·.size) a.toList ∧
  a.all (fun x => List.Pairwise (· ≤ ·) x.toList) ∧
  (List.range (a[0]!.size)).all (fun i =>
    List.Pairwise (· ≤ ·) (a.map (fun x => x[i]!)).toList
  )
  -- !benchmark @end precond

def SlopeSearch_postcond (a : Array (Array Int)) (key : Int) (result: (Int × Int)) (h_precond : SlopeSearch_precond (a) (key)) :=
  -- !benchmark @start postcond
  let (m, n) := result;
  (m ≥ 0 ∧ m < a.size ∧ n ≥ 0 ∧ n < (a[0]!).size ∧ get2d a m n = key) ∨
  (m = -1 ∧ n = -1 ∧ a.all (fun x => x.all (fun e => e ≠ key)))
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

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

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array (Array Int)) (key : Int):
  VerinaSpec.SlopeSearch_precond a key ↔ LeetProofSpec.precondition a key := by
  sorry

theorem postcondition_equiv (a : Array (Array Int)) (key : Int) (result : (Int × Int)) (h_precond : VerinaSpec.SlopeSearch_precond a key):
  VerinaSpec.SlopeSearch_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result := by
  sorry
