import Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    lastDigit: extract the last decimal digit of a non-negative integer.
    Natural language breakdown:
    1. Input n is a natural number (hence non-negative by type).
    2. The last digit in base 10 is the remainder when dividing n by 10.
    3. The result must be a natural number between 0 and 9 inclusive.
    4. The returned digit must satisfy: result = n % 10.
-/

section Impl
method lastDigit (n : Nat) return (result : Nat)
  ensures result = n % 10
  ensures result < 10
  do
    let d := n % 10
    return d
end Impl

section Proof
set_option maxHeartbeats 10000000

-- prove_correct lastDigit by
  -- loom_solve <;> (try simp at *; expose_names)

prove_correct lastDigit by
  loom_solve
end Proof
