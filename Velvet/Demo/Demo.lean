----------------------------------------------------
-- Example 1: Velvet basics
----------------------------------------------------

import Velvet.Std
import CaseStudies.TestingUtil

section squareRoot

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver "grind"
set_option loom.solver.smt.timeout 1

-- (1) Proving things with SMT
-- partial correctness version of square root
method sqrt (x: ℕ) return (res: ℕ)
  ensures res * res ≤ x
  ensures ∀ i, i ≤ res → i * i ≤ x
  ensures ∀ i, i * i ≤ x → i ≤ res
  do
    if x = 0 then
      return 0
    else
      let mut i := 0
      while i * i  ≤ x
      invariant ∀ j, j < i → j * j ≤ x
      do
        i := i + 1
      return i - 1
prove_correct sqrt by
  loom_solve
  {
    intros i h
    subst_vars
    exact Nat.mul_self_le_mul_self_iff.mp h
  }
  all_goals loom_smt

-- #eval sqrt 10 |>.extract

variable [FinEnum α]

method Predicate.toArray (mut s: α -> Bool) return (res: Array α)
  ensures ∀ x, sOld x <-> x ∈ res
  do
    let mut res := #[]
    while ∃ x, s x
    invariant ∀ x, sOld x = true <-> (x ∈ res ∨ s x)
    do
      let x :| s x
      res := res.push x
      s := fun y => if y = x then false else s y
    return res

#eval Predicate.toArray (fun x => x ∈ #[1, 2, (3 : Fin 6)]) |>.extract.1

prove_correct Predicate.toArray by
  loom_solve

method balanceWithdraw (mut balance : Nat) return (success: Bool)
  ensures success = true
  do
    let mut success := true
    let (amounts : List Nat) :| amounts.sum <= balance
    let mut queue := amounts
    while queue.length > 0
    invariant queue.sum <= balance
    invariant success = true
    do
      if balance < queue.head! then
        success := false; break
      else
        balance := balance - queue.head!
        queue := queue.tail
    return success

attribute [simp] List.sum

prove_correct balanceWithdraw by
  loom_solve <;> simp_all
  all_goals cases queue <;> simp_all; grind

set_option loom.semantics.choice "angelic"

method balanceWithdraw' (mut balance : Nat) return (success: Bool)
  ensures success = false
  do
    let mut success := true
    let amounts ← pick (List Nat)
    let mut queue := amounts
    while queue.length > 0
    invariant queue.head! > balance
    done_with success = false
    do
      if balance < queue.head! then
        success := false; break
      else
        balance := balance - queue.head!
        queue := queue.tail
    return success

attribute [grind] List.eq_nil_iff_length_eq_zero

prove_correct balanceWithdraw' by
  loom_solve
  { (have : queue = [] := by grind); simp_all }
  exists [balanceOld + 1]; simp

end squareRoot
