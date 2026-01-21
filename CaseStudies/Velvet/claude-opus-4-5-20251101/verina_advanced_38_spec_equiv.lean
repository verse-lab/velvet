import Lean
import Mathlib.Tactic


namespace VerinaSpec

def maxCoverageAfterRemovingOne_precond (intervals : List (Prod Nat Nat)) : Prop :=
  -- !benchmark @start precond
  intervals.length > 0

-- !benchmark @end precond

def maxCoverageAfterRemovingOne_postcond (intervals : List (Prod Nat Nat)) (result: Nat) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) : Prop :=
  -- !benchmark @start postcond
  ∃ i < intervals.length,
    let remaining := List.eraseIdx intervals i
    let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1)
    let merged := sorted.foldl (fun acc curr =>
      match acc with
      | [] => [curr]
      | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
    ) []
    let cov := merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
    result = cov ∧
    ∀ j < intervals.length,
      let rem_j := List.eraseIdx intervals j
      let sort_j := List.mergeSort rem_j (fun (a b : Nat × Nat) => a.1 ≤ b.1)
      let merged_j := sort_j.foldl (fun acc curr =>
        match acc with
        | [] => [curr]
        | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
      ) []
      let cov_j := merged_j.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
      cov ≥ cov_j

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Define the set of points covered by a list of intervals
def coveredSet (intervals : List (Nat × Nat)) : Set Nat :=
  {x | ∃ interval ∈ intervals, interval.1 ≤ x ∧ x < interval.2}

-- Remove element at index i from a list
def removeAt (l : List α) (i : Nat) : List α :=
  l.take i ++ l.drop (i + 1)

-- Precondition: at least one interval
def precondition (intervals : List (Nat × Nat)) :=
  intervals.length ≥ 1

-- Postcondition clauses:
-- 1. The result equals the coverage (cardinality of covered set) obtainable by removing some interval
def ensures1 (intervals : List (Nat × Nat)) (result : Nat) :=
  ∃ i : Nat, i < intervals.length ∧ result = Nat.card (coveredSet (removeAt intervals i))

-- 2. The result is at least as large as any coverage after removing any single interval
def ensures2 (intervals : List (Nat × Nat)) (result : Nat) :=
  ∀ i : Nat, i < intervals.length → Nat.card (coveredSet (removeAt intervals i)) ≤ result

def postcondition (intervals : List (Nat × Nat)) (result : Nat) :=
  ensures1 intervals result ∧ ensures2 intervals result

end LeetProofSpec

def precondition_equiv (intervals : List (Prod Nat Nat)):
  VerinaSpec.maxCoverageAfterRemovingOne_precond intervals ↔ LeetProofSpec.precondition intervals := by
  sorry

def postcondition_equiv (intervals : List (Prod Nat Nat)) (result: Nat) (h_precond : VerinaSpec.maxCoverageAfterRemovingOne_precond (intervals)) :
  VerinaSpec.maxCoverageAfterRemovingOne_postcond intervals result h_precond ↔ LeetProofSpec.postcondition intervals result := by
  sorry
