import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    firstDuplicate: Find the first duplicate integer in a list when scanning left to right
    Natural language breakdown:
    1. We are given a list of integers
    2. We scan from left to right, looking for the first element that has appeared before
    3. "First duplicate" means the first position j where lst[j] equals some earlier lst[i] (i < j)
    4. We want to find the smallest index j such that lst[j] appears in lst[0..j-1]
    5. The result is the value at that index j
    6. If no such duplicate exists, return none
    7. Edge cases:
       - Empty list: no duplicates, return none
       - Single element: no duplicates, return none
       - All distinct elements: return none
       - Multiple duplicates: return the one with earliest second occurrence
    8. Key insight: We're looking for the first index j where (List.take j lst).contains lst[j]!
-/

section Impl
method firstDuplicate (lst: List Int)
  return (result: Option Int)
  ensures match result with
  | none =>
      -- No element appears in its prefix (no duplicates)
      ∀ j : Nat, j < lst.length → ¬((lst.take j).contains lst[j]!)
  | some x =>
      -- There exists a position j where:
      -- 1. lst[j]! = x
      -- 2. x appears in the prefix lst[0..j-1]
      -- 3. j is minimal (no earlier position has an element appearing in its prefix)
      ∃ j : Nat, j < lst.length ∧
                 lst[j]! = x ∧
                 (lst.take j).contains x ∧
                 (∀ k : Nat, k < j → ¬((lst.take k).contains lst[k]!))
  do
  let mut i := 0
  let mut found : Option Int := none
  while i < lst.length ∧ found = none
    -- Invariant 1: Index bounds
    -- Init: i = 0, so 0 ≤ i ≤ lst.length holds
    -- Pres: i increments only when i < lst.length, so i ≤ lst.length maintained
    invariant "i_bounds" 0 ≤ i ∧ i ≤ lst.length
    -- Invariant 2: No duplicates found in prefix [0..i)
    -- Init: i = 0, vacuously true
    -- Pres: We only increment i when lst[i]! is not in lst.take i
    invariant "no_dup_prefix" found = none → (∀ k : Nat, k < i → ¬((lst.take k).contains lst[k]!))
    -- Invariant 3: When found = some x, x is the first duplicate with witness
    -- Init: found = none, so vacuously true
    -- Pres: When we set found := some current, current = lst[i]! and (lst.take i).contains current
    invariant "found_valid" ∀ x, found = some x →
      (∃ j : Nat, j < lst.length ∧ j ≤ i ∧ lst[j]! = x ∧ (lst.take j).contains x ∧
        (∀ k : Nat, k < j → ¬((lst.take k).contains lst[k]!)))
    done_with i = lst.length ∨ found ≠ none
  do
    let current := lst[i]!
    let prefixList := lst.take i
    if prefixList.contains current then
      found := some current
    else
      i := i + 1
  return found
end Impl

section Proof

prove_correct firstDuplicate by
  loom_solve
end Proof
