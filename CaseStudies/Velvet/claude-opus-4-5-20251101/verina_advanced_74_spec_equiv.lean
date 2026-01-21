import Lean
import Mathlib.Tactic
import Std.Data.HashSet


open Std

namespace VerinaSpec

@[reducible]
def solution_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  1 ≤ nums.length ∧ nums.length ≤ 100 ∧ nums.all (fun x => 1 ≤ x ∧ x ≤ 100)

-- !benchmark @end precond

@[reducible]
def solution_postcond (nums : List Nat) (result: Nat) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length;

  let getSubarray_local := fun (i j : Nat) =>
    (nums.drop i).take (j - i + 1);

  let distinctCount_local := fun (l : List Nat) =>
    let foldFn := fun (seen : List Nat) (x : Nat) =>
      if seen.elem x then seen else x :: seen;
    let distinctElems := l.foldl foldFn [];
    distinctElems.length;

  let square_local := fun (n : Nat) => n * n;

  (1 <= n ∧ n <= 100 ∧ nums.all (fun x => 1 <= x ∧ x <= 100)) ->
  (
    result >= 0
    ∧
    let expectedSum : Nat :=
      List.range n |>.foldl (fun (outerSum : Nat) (i : Nat) =>
        let innerSum : Nat :=
          List.range (n - i) |>.foldl (fun (currentInnerSum : Nat) (d : Nat) =>
            let j := i + d;
            let subarr := getSubarray_local i j;
            let count := distinctCount_local subarr;
            currentInnerSum + square_local count
          ) 0
        outerSum + innerSum
      ) 0;

    result = expectedSum
  )

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to extract a subarray (contiguous portion) from a list
-- subarray l i j returns elements from index i to j (inclusive)
def subarray (l : List Nat) (i : Nat) (j : Nat) : List Nat :=
  (l.drop i).take (j - i + 1)

-- Helper function to count distinct elements in a list using toFinset cardinality
def distinctCount (l : List Nat) : Nat :=
  l.toFinset.card

-- Helper function to compute squared distinct count for a subarray
def squaredDistinctCount (l : List Nat) (i : Nat) (j : Nat) : Nat :=
  let sub := subarray l i j
  let d := distinctCount sub
  d * d

-- Precondition: list is non-empty, length at most 100, elements between 1 and 100
def precondition (nums : List Nat) :=
  1 ≤ nums.length ∧ nums.length ≤ 100 ∧ nums.all (fun x => 1 ≤ x ∧ x ≤ 100)

-- Postcondition: result equals sum of squared distinct counts over all subarrays
-- A subarray is defined by indices (i, j) where 0 ≤ i ≤ j < nums.length
-- Using Finset.sum for a declarative mathematical specification
def postcondition (nums : List Nat) (result : Nat) :=
  result = (Finset.range nums.length).sum (fun i =>
           (Finset.Icc i (nums.length - 1)).sum (fun j =>
           squaredDistinctCount nums i j))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (nums : List Nat):
  VerinaSpec.solution_precond nums ↔ LeetProofSpec.precondition nums := by
  rfl

theorem postcondition_equiv (nums : List Nat) (result : Nat):
  VerinaSpec.solution_postcond nums result ↔ LeetProofSpec.postcondition nums result := by
  sorry
