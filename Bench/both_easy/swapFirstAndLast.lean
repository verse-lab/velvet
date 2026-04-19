import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    swapFirstAndLast: swap the first and last elements of a non-empty array of integers.
    Natural language breakdown:
    1. Input is an array `a : Array Int`.
    2. The input array is assumed to be non-empty (size > 0).
    3. The output is a new array with the same size as the input.
    4. The element at index 0 of the output equals the last element of the input (index a.size - 1).
    5. The element at the last index of the output equals the first element of the input (index 0).
    6. Every element at an index strictly between 0 and the last index is unchanged.
    7. Special case: if the array has size 1, swapping first and last leaves the array unchanged.
-/

-- Helper: the last index of a non-empty array (as a Nat)
@[grind]
def lastIdx (a : Array Int) : Nat := a.size - 1

section Impl
method swapFirstAndLast (a : Array Int) return (result : Array Int)
  require 0 < a.size
  ensures result.size = a.size
  ensures (∀ (i : Nat), i < a.size →
          (result[i]! =
            if i = 0 then a[lastIdx a]!
            else if i = lastIdx a then a[0]!
            else a[i]!))
  do
    let n := a.size
    let last := n - 1
    let mut result := a
    -- If size is 1, swapping first/last is identity; otherwise perform a swap.
    if n = 1 then
      return result
    else
      let firstVal := a[0]!
      let lastVal := a[last]!
      result := result.set! 0 lastVal
      result := result.set! last firstVal
      return result
end Impl

section Proof
set_option maxHeartbeats 10000000

-- prove_correct swapFirstAndLast by
  -- loom_solve <;> (try simp at *; expose_names)

prove_correct swapFirstAndLast by
  loom_solve
end Proof
