import Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- The Euclidean algorithm for GCD is a classic example of a function requiring
-- explicit termination measures due to the modulo operation

method gcd (a : Nat) (b : Nat) return (res : Nat)
  require a > 0
  ensures res > 0
  do
    if b = 0 then
      return a
    else
      let remainder := a % b
      let result ← gcd b remainder
      return result
  termination_by b
  decreasing_by
    apply Nat.mod_lt
    grind

attribute [solverHint] Nat.mod_lt

prove_correct gcd
termination_by b
decreasing_by all_goals(
  -- Looking at the goals, we can see the precondition is in the context
  -- We need to extract b > 0 from the WithName wrapper
  apply Nat.mod_lt
  grind
  )
by
  loom_solve
