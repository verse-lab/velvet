import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

macro_rules
| `(tactic|loom_solver) => `(tactic|first | grind | loom_smt [*])

/- Problem Description
    isPrime: Determine whether a given natural number is prime.
    Natural language breakdown:
    1. The input is a natural number n, and the task assumes n ≥ 2.
    2. A natural number n is prime iff it has no divisor k with 1 < k < n.
    3. Equivalently: n is prime iff for every k with 1 < k < n, k does not divide n.
    4. The method returns a Bool: true exactly when n is prime, and false otherwise.
    5. Inputs that violate n ≥ 2 are outside the intended domain.
-/

section Impl
method isPrime (n : Nat) return (result : Bool)
  require 2 ≤ n
  ensures result = true ↔ ¬ ∃ k : Nat, 1 < k ∧ k < n ∧ n % k = 0
  do
  -- Brute-force check for any divisor k with 2 ≤ k < n.
  -- If we find one, n is composite.
  let mut k : Nat := 2
  let mut composite : Bool := false
  while k < n ∧ composite = false
    -- Invariant: k stays within bounds; needed for modular reasoning and to show progress.
    -- Initialization: k = 2 and precondition gives 2 ≤ n, so k ≤ n.
    -- Preservation: k only increases by 1 when composite stays false; otherwise k unchanged.
    invariant "inv_bounds" (2 ≤ k ∧ k ≤ n)
    -- Invariant: when we mark composite, we have actually found a nontrivial divisor of n.
    -- Initialization: composite = false, so vacuously true.
    -- Preservation: the only assignment setting composite := true happens under guard n % k = 0,
    -- giving witness k; k < n follows from loop guard k < n.
    invariant "inv_composite_witness" (composite = true → ∃ d : Nat, 1 < d ∧ d < n ∧ n % d = 0)
    -- Invariant: if we have not marked composite yet, then no nontrivial divisor has been found
    -- among all candidates in [2, k).
    -- Initialization: k = 2 makes the range empty.
    -- Preservation: when n % k ≠ 0, we increment k, extending the checked range by one.
    -- If n % k = 0, we set composite := true, so antecedent composite = false is false.
    invariant "inv_checked" (composite = false → ∀ d : Nat, 2 ≤ d ∧ d < k → n % d ≠ 0)
    done_with (k = n ∨ composite = true)
  do
    if n % k = 0 then
      composite := true
    else
      k := k + 1
  if composite = true then
    return false
  else
    return true
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct isPrime by
  loom_solve


end Proof
