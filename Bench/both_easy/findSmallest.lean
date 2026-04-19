import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findSmallest: Find the smallest number in an array of natural numbers
    Natural language breakdown:
    1. Given an array of natural numbers, find the smallest element
    2. If the array is empty, return none
    3. If the array is non-empty, return some(min) where min is the smallest element
    4. The smallest element must be in the array
    5. The smallest element must be less than or equal to all other elements
    6. For non-empty arrays, the result uniquely identifies the minimum value
    7. This is a property-based specification: we specify what the minimum must satisfy
       (membership and minimality), not how to compute it
    8. Edge cases:
       - Empty array: return none
       - Single element: return that element
       - All equal elements: return that common value
       - Array with duplicates of minimum: return the minimum value
-/

section Impl

method findSmallest (s: Array Nat)
  return (result: Option Nat)
  ensures match result with
  | none => s.size = 0
  | some min =>
      s.size > 0 ∧
      (∃ i, i < s.size ∧ s[i]! = min) ∧
      (∀ j, j < s.size → min ≤ s[j]!)
  do
  if s.size = 0 then
    return none
  else
    let mut minIndex := 0
    let mut i := 1
    while i < s.size
      -- Invariant 1: i stays in valid range starting from 1
      -- Initialization: i = 1 at entry, which satisfies 1 ≤ 1 ≤ s.size (since s.size > 0)
      -- Preservation: i increments but stays ≤ s.size due to loop condition
      invariant 1 ≤ i ∧ i ≤ s.size
      -- Invariant 2: minIndex points to a valid index in the scanned portion
      -- Initialization: minIndex = 0 < 1 = i holds at entry
      -- Preservation: when updated, minIndex becomes i (before increment), maintaining minIndex < i+1
      invariant 0 ≤ minIndex ∧ minIndex < i
      -- Invariant 3: minIndex is always a valid array index
      -- Follows from invariant 2 and i ≤ s.size
      invariant minIndex < s.size
      -- Invariant 4: s[minIndex] is the minimum of all elements scanned so far [0..i)
      -- Initialization: At i=1, only s[0] scanned, and minIndex=0, so s[minIndex]! ≤ s[0]! trivially holds
      -- Preservation: If s[i]! < s[minIndex]!, we update minIndex to i, maintaining property for [0..i+1)
      --               Otherwise, s[minIndex]! ≤ s[i]! already, so property holds for [0..i+1)
      -- Sufficiency: When i = s.size, this gives us the global minimum and its index
      invariant ∀ j, 0 ≤ j ∧ j < i → s[minIndex]! ≤ s[j]!
      done_with i = s.size
    do
      if s[i]! < s[minIndex]! then
        minIndex := i
      else
        pure ()
      i := i + 1
    return some s[minIndex]!

end Impl

section Proof

prove_correct findSmallest by
  loom_solve

end Proof
