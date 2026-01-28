import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isGreater: determine if an integer is strictly greater than every element in an array
    Natural language breakdown:
    1. Inputs are an integer n and an array a of integers.
    2. The method returns a Boolean.
    3. The result is true exactly when n is strictly greater than every element in a.
    4. The result is false when there exists at least one element x in a with x ≥ n.
    5. Empty arrays are rejected (see reject input).
-/

section Impl
method isGreater (n : Int) (a : Array Int)
  return (result : Bool)
  require a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
  do
    let mut ok := true
    let mut i : Nat := 0
    while i < a.size
      -- Invariant 1 (bounds): i stays within the array bounds, so a[i]! is safe when the guard holds.
      -- Init: i=0 so 0 ≤ i ≤ a.size. Preserved: i increases by 1 but loop guard ensures i < a.size.
      invariant "inv_bounds" (0 ≤ i ∧ i ≤ a.size)
      -- Invariant 2 (meaning of ok): ok is true iff all elements seen so far are < n.
      -- Init: i=0, the range is empty so the ∀ is true, hence ok=true matches. Preserved: each step updates ok
      -- to false exactly when encountering a counterexample at index i.
      invariant "inv_ok_prefix" (ok = true ↔ (∀ j : Nat, j < i → a[j]! < n))
    do
      if a[i]! < n then
        ok := ok
      else
        ok := false
      i := i + 1
    return ok
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct isGreater by
  loom_solve <;> (try simp at *; expose_names)
end Proof
