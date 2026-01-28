import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    containsConsecutiveNumbers: determine whether an array of integers contains at least one pair of consecutive numbers
    Natural language breakdown:
    1. Input is an array `a` of integers; it may be empty or non-empty.
    2. A "consecutive pair" means there exists an index `i` such that `i + 1 < a.size` and `a[i] + 1 = a[i+1]`.
    3. The result is `true` iff such an index exists.
    4. If the array has size 0 or 1, then no such index exists and the result is `false`.
    5. There are no preconditions.
-/

-- Helper predicate: there exists an adjacent index with successor-by-1 relation.
-- Using Nat indices with bounds and `a[i]!` access as required by the guidelines.
@[grind]
def HasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!

section Impl
method containsConsecutiveNumbers (a : Array Int)
  return (result : Bool)
  ensures result = true ↔ HasConsecutivePair a
  do
    if a.size < 2 then
      return false
    else
      let mut i : Nat := 0
      let mut found : Bool := false
      while i + 1 < a.size ∧ found = false
        -- Bounds: loop condition gives i+1 < a.size; keep a weaker, stable form.
        invariant "inv_bounds" (i + 1 ≤ a.size)
        -- Progress information: as long as we haven't found a pair, indices before i are checked.
        invariant "inv_no_pair_so_far" (found = false → (∀ j : Nat, j < i → a[j]! + 1 ≠ a[j + 1]!))
        -- If found is true, we have a witness consecutive pair.
        invariant "inv_found_witness" (found = true → HasConsecutivePair a)
        done_with (i + 1 ≥ a.size ∨ found = true)
      do
        if a[i]! + 1 = a[i + 1]! then
          found := true
        else
          i := i + 1
      return found
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct containsConsecutiveNumbers by
  loom_solve_async
end Proof
