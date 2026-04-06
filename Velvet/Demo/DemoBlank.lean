----------------------------------------------------
-- Example 1: Velvet basics
----------------------------------------------------

import Velvet.Std
import CaseStudies.TestingUtil

section squareRoot

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver "cvc5"
set_option loom.solver.smt.timeout 1

method sqrt (x: ℕ) return (res: ℕ)
  ensures True
  do
    return 0
prove_correct sqrt by
  sorry

-- #eval sqrt 10 |>.extract

variable [FinEnum α]

method Predicate.toArray (mut s: α -> Bool) return (res: Array α)
  ensures True
  do
    return #[]

#eval Predicate.toArray (fun x => x ∈ #[1, 2, (3 : Fin 6)]) |>.extract.1

prove_correct Predicate.toArray by
  sorry

method balanceWithdraw (mut balance : Nat) return (success: Bool)
  ensures True
  do
    return true

prove_correct balanceWithdraw by
  sorry

set_option loom.semantics.choice "angelic"

method balanceWithdraw' (mut balance : Nat) return (success: Bool)
  ensures success = false
  do
    return false

attribute [grind] List.eq_nil_iff_length_eq_zero

prove_correct balanceWithdraw' by
  sorry

end squareRoot
