import CaseStudies.Velvet.Std
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    sumOfDigits: compute the sum of the base-10 digits of a non-negative integer.
    Natural language breakdown:
    1. The input n is a natural number (a non-negative integer).
    2. Consider the canonical base-10 digit list of n given by Mathlib: `Nat.digits 10 n`.
       This list is in little-endian order (least-significant digit first).
    3. Each element of `Nat.digits 10 n` is a digit in the range 0..9.
    4. The output is the sum of these digits.
    5. In particular, for n = 0, the digit list is empty and the sum is 0.
    6. The result is a natural number.
-/

section Specs
-- No special precondition: input is already a Nat.
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: result is exactly the sum of the canonical base-10 digits.
-- Using `Nat.digits` makes the specification canonical and uniquely determines the result.
def postcondition (n : Nat) (result : Nat) : Prop :=
  result = (Nat.digits 10 n).sum
end Specs

section Impl
method sumOfDigits (n : Nat) return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  let mut t := n
  let mut s : Nat := 0
  while t > 0
    -- Invariant: accumulator tracks the sum of digits already removed from `t`.
    -- Initialization: `t = n`, so removed prefix is `[]` and sum is 0.
    -- Preservation: writing `t = 10*q + r` with `r = t % 10`, `q = t / 10`, we add `r` to `s` and set `t := q`.
    -- Sufficiency: on exit `t = 0`, the removed digits are exactly `Nat.digits 10 n`, hence `s` is their sum.
    invariant "sumOfDigits_acc" s + (Nat.digits 10 t).sum = (Nat.digits 10 n).sum
  do
    let d := t % 10
    s := s + d
    t := t / 10
  return s
end Impl

section Proof
set_option maxHeartbeats 10000000

-- prove_correct sumOfDigits by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (require_1 : precondition n)
    (s : ℕ)
    (t : ℕ)
    (invariant_sumOfDigits_acc : s + (Nat.digits 10 t).sum = (Nat.digits 10 n).sum)
    (if_pos : 0 < t)
    : s + t % 10 + (Nat.digits 10 (t / 10)).sum = (Nat.digits 10 n).sum := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_1
    (n : ℕ)
    (require_1 : precondition n)
    (s : ℕ)
    (t : ℕ)
    (invariant_sumOfDigits_acc : s + (Nat.digits 10 t).sum = (Nat.digits 10 n).sum)
    (i : ℕ)
    (t_1 : ℕ)
    (done_1 : t = 0)
    (i_1 : s = i ∧ t = t_1)
    : postcondition n i := by
    -- unfold the postcondition
    unfold postcondition
    -- extract s = i from the bookkeeping conjunction
    have hsi : s = i := i_1.left
    -- use the invariant at termination t = 0
    have hs : s = (Nat.digits 10 n).sum := by
      have := invariant_sumOfDigits_acc
      -- substitute t = 0 and simplify digits/sum
      -- Nat.digits 10 0 = [] and ([]).sum = 0, so s + 0 = ...
      simpa [done_1] using this
    -- transfer from s to i
    exact (Eq.symm hsi).trans hs

prove_correct sumOfDigits by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n require_1 s t invariant_sumOfDigits_acc if_pos)
  exact (goal_1 n require_1 s t invariant_sumOfDigits_acc i t_1 done_1 i_1)
end Proof
