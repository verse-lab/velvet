/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8555f546-b814-4b9c-8eff-b0779328fc27

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (nums : List Nat) (result : Nat) (h_precond: VerinaSpec.solution_precond nums):
  VerinaSpec.solution_postcond nums result ↔ LeetProofSpec.postcondition nums result
-/

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

theorem postcondition_equiv (nums : List Nat) (result : Nat) (h_precond: VerinaSpec.solution_precond nums):
  VerinaSpec.solution_postcond nums result ↔ LeetProofSpec.postcondition nums result := by
  unfold VerinaSpec.solution_postcond LeetProofSpec.postcondition;
  -- By definition of `List.foldl`, we can rewrite the left-hand side of the equivalence to match the right-hand side.
  have h_foldl_sum : ∀ (n : ℕ) (f : ℕ → ℕ), List.foldl (fun acc i => acc + f i) 0 (List.range n) = Finset.sum (Finset.range n) f := by
    intro n f; induction' n with n ih <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ] ;
  -- Apply the equivalence of foldl and sum to the outer sum.
  have h_outer_sum : List.foldl (fun outerSum i => outerSum + List.foldl (fun currentInnerSum d => currentInnerSum + (List.foldl (fun seen x => if List.elem x seen = Bool.true then seen else x :: seen) [] (List.take (i + d - i + 1) (List.drop i nums))).length * (List.foldl (fun seen x => if List.elem x seen = Bool.true then seen else x :: seen) [] (List.take (i + d - i + 1) (List.drop i nums))).length) 0 (List.range (nums.length - i))) 0 (List.range nums.length) = Finset.sum (Finset.range nums.length) (fun i => Finset.sum (Finset.Icc i (nums.length - 1)) (fun j => (List.foldl (fun seen x => if List.elem x seen = Bool.true then seen else x :: seen) [] (List.take (j - i + 1) (List.drop i nums))).length * (List.foldl (fun seen x => if List.elem x seen = Bool.true then seen else x :: seen) [] (List.take (j - i + 1) (List.drop i nums))).length)) := by
    rw [ h_foldl_sum ];
    refine' Finset.sum_congr rfl fun i hi => _;
    erw [ Finset.sum_Ico_eq_sum_range ];
    grind;
  -- The length of the list obtained by folding the seen list is equal to the cardinality of the Finset created from that list.
  have h_foldl_length : ∀ (l : List ℕ), (List.foldl (fun seen x => if List.elem x seen = Bool.true then seen else x :: seen) [] l).length = l.toFinset.card := by
    -- We can prove this by induction on the list.
    intro l
    induction' l using List.reverseRecOn with x l ih;
    · rfl;
    · by_cases h : l ∈ x.toFinset <;> simp_all +decide [ List.toFinset_append ];
      · -- Since $l$ is in $x$, it will be added to the seen list during the foldl process. Therefore, the length of the list after folding is the same as the cardinality of the Finset created from $x$.
        have h_foldl_length : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ∈ List.foldl (fun (seen : List ℕ) (x : ℕ) => if x ∈ seen then seen else x :: seen) [] l := by
          intro l x hx; induction' l using List.reverseRecOn with x l ih <;> aesop;
        rw [ if_pos ( h_foldl_length x l h ), ih ];
      · rw [ if_neg ];
        · rw [ List.length_cons, ih ];
        · have h_foldl_not_in : ∀ (l : List ℕ) (x : ℕ), x ∉ l → x ∉ List.foldl (fun seen x => if x ∈ seen then seen else x :: seen) [] l := by
            intro l x hx; induction' l using List.reverseRecOn with x l ih <;> aesop;
          exact h_foldl_not_in x l h;
  simp_all +decide [ LeetProofSpec.squaredDistinctCount ];
  unfold LeetProofSpec.distinctCount LeetProofSpec.subarray; aesop;
