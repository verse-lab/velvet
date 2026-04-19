import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findMajorityElement: Find the majority element in a list of integers
    Natural language breakdown:
    1. We are given a list of integers (may include duplicates and negative numbers)
    2. A majority element is defined as an element that appears strictly more than half the number of times in the list
    3. Formally, element x is a majority element if lst.count x > lst.length / 2
    4. If such a majority element exists, return that element
    5. If no majority element exists, return -1
    6. Edge case: Empty list has no majority element, return -1
    7. Note: There can be at most one majority element in any list (since it must appear more than half the time)
    8. The result is either the unique majority element or -1
-/

-- Helper function to check if an element is a majority element
@[grind]
def isMajorityElement (lst : List Int) (x : Int) : Prop :=
  lst.count x > lst.length / 2

-- Helper function to check if a majority element exists
@[grind]
def hasMajorityElement (lst : List Int) : Prop :=
  ∃ x, x ∈ lst ∧ isMajorityElement lst x

section Impl
method findMajorityElement (lst : List Int)
  return (result : Int)
  ensures hasMajorityElement lst → (result ∈ lst ∧ isMajorityElement lst result)
  ensures ¬hasMajorityElement lst → result = -1
  do
  let n := lst.length
  let threshold := n / 2
  let mut i := 0
  let mut found := false
  let mut candidate : Int := -1

  while i < n
    -- i is bounded by list length
    invariant "i_bounds" 0 ≤ i ∧ i ≤ n
    -- found implies candidate is a majority element in the list
    invariant "found_implies_majority" found = true → (candidate ∈ lst ∧ isMajorityElement lst candidate)
    -- not found implies no majority element among first i elements
    invariant "not_found_checked" found = false → (∀ k : Nat, k < i → ¬isMajorityElement lst lst[k]!)
    done_with i >= n
  do
    let elem := lst[i]!
    let mut count := 0
    let mut j := 0

    -- Count occurrences of elem in lst
    while j < n
      -- j is bounded by list length
      invariant "j_bounds" 0 ≤ j ∧ j ≤ n
      -- count equals occurrences of elem in lst[0..j]
      invariant "count_correct" count = (lst.take j).count elem
      -- preserve outer loop invariants
      invariant "found_preserved" found = true → (candidate ∈ lst ∧ isMajorityElement lst candidate)
      invariant "i_preserved" 0 ≤ i ∧ i < n
      invariant "elem_in_list" i < lst.length → elem = lst[i]!
      invariant "not_found_checked_inner" found = false → (∀ k : Nat, k < i → ¬isMajorityElement lst lst[k]!)
      done_with j >= n
    do
      if lst[j]! = elem then
        count := count + 1
      j := j + 1

    -- Check if this element is a majority
    if count > threshold then
      found := true
      candidate := elem

    i := i + 1

  if found then
    return candidate
  else
    return -1
end Impl

section Proof
set_option maxHeartbeats 10000000

attribute [grind] List.take_succ_eq_append_getElem

prove_correct findMajorityElement by
  loom_solve
end Proof
