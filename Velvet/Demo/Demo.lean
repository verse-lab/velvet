----------------------------------------------------
-- Example 1: Velvet basics
----------------------------------------------------

import Velvet.Std
import CaseStudies.TestingUtil

section squareRoot

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- (1) SMT-backed vs. interactive proving
--
-- Computes the integer square root of `x`: the largest `res` with `res * res ≤
-- x`. The specification pins down `res` exactly (largest lower bound), and the
-- loop searches for it.
--
-- The point: most of the verification is discharged automatically by an SMT
-- solver, and only the one goal SMT cannot close is proved by hand.
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

#eval sqrt 10 |>.extract

set_option loom.solver "grind"
set_option loom.solver.smt.timeout 1

-- The proof is a hybrid: `loom_solve` sets up the verification conditions, the
-- one goal that needs a nonlinear fact about squares is closed interactively
-- (the `{ … }` block), and every remaining VC is handed to the SMT solver via
-- `loom_smt`.
prove_correct sqrt by
  -- loom_goals_intro
  -- loom_unfold
  loom_solve
  {
    -- Interactive step: SMT (typically) cannot see this monotonicity fact about
    -- squaring.
    intros i h
    subst_vars
    exact Nat.mul_self_le_mul_self_iff.mp h
  }
  -- Everything else is discharged by SMT.
  all_goals loom_smt

variable [FinEnum α]

-- (2) Reasoning about non-determinism
--
-- Reifies a decidable predicate `s` over a finite type into an array holding
-- exactly the elements it accepts. Each iteration picks *some* remaining
-- witness and removes it.
--
-- The point: the postcondition holds regardless of *which* witness the choice
-- yields: correctness is proved for the non-deterministic pick, not a fixed
-- enumeration order.
method Predicate.toArray (mut s: α -> Bool) return (res: Array α)
  ensures ∀ x, sOld x <-> x ∈ res
  do
    let mut res := #[]
    while ∃ x, s x
    invariant ∀ x, sOld x = true <-> (x ∈ res ∨ s x)
    do
      let x :| s x               -- non-deterministic choice: any `x` with `s x`
      res := res.push x
      s := fun y => if y = x then false else s y
    return res

#eval Predicate.toArray (fun x => x ∈ #[1, 2, (3 : Fin 6)]) |>.extract.1

prove_correct Predicate.toArray by
  loom_solve

-- (3) Demonic non-determinism — the ∀ (forall) reading of choice
--
-- Withdraws a non-deterministically chosen list of `amounts` from a `balance`,
-- one at a time. The choice is *demonic* (`loom.semantics.choice "demonic"`
-- above): an adversary picks the amounts.
--
-- The point: we prove `success = true` holds for *every* list whose sum fits
-- within the balance — the guarantee must survive any choice.
method balanceWithdraw (mut balance : Nat) return (success: Bool)
  ensures success
  do
    let mut success := true
    let (amounts : List Nat) :| amounts.sum <= balance   -- adversary chooses; must hold ∀
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

-- (4) Angelic non-determinism — the ∃ (exists) reading of choice
--
-- The same withdrawal loop, but now the choice is *angelic*
-- (`loom.semantics.choice "angelic"`): we get to pick the `amounts` in our
-- favour.
--
-- The point: we prove `success = false` is *achievable* — it suffices to
-- exhibit one list of amounts that forces failure, and the proof supplies that
-- witness explicitly.
set_option loom.semantics.choice "angelic"

method balanceWithdraw' (mut balance : Nat) return (success: Bool)
  ensures ¬ success
  do
    let mut success := true
    let amounts ← pick (List Nat)        -- we choose; suffices to hold for ∃ one list
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
  exists [balanceOld + 1]; simp   -- the witness: one over-budget amount forces failure

end squareRoot
