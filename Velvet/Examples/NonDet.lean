module

public import Velvet
public meta import Velvet

open Std.WP Lean.Order

namespace Velvet.Examples.NonDet

/-!
# Non-determinism in Velvet (`NonDetT`)

This module demonstrates both **Demonic** and **Angelic** non-determinism in Velvet.
Computations are written using Velvet's native `method` frontend, overriding the
monad stack via `in DemonicT Option` or `in AngelicT Option`.

Features demonstrated:
1. **Hilbert Choice Operator**: `let x :| p` inside `do` blocks.
2. **Demonic Verification**: Universal choice semantics (`⨅`), verified automatically with `velvet_vcgen [...] with finish`.
3. **Angelic Verification**: Existential choice semantics (`⨆`), verified with `velvet_vcgen`.
4. **Non-deterministic Loops**: Loops verified using `while'` with invariants, termination metrics, and `done_with`.
5. **Constructive Extraction**: Evaluation of non-deterministic methods via `.run`.
-/

/- ============================================================================
   1. Demonic Non-Determinism (`DemonicT Option`)
   ============================================================================ -/

/-- Demonic choice using the Hilbert choice operator `let x :| p`.
The specification requires `res > inp + 10`. The program picks an answer
satisfying `ans > inp + 200`, which universally satisfies the postcondition. -/
method pickGreater (inp : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res > inp + 10
do
  let (ans : Nat) :| ans > inp + 200
  return ans

prove_correct pickGreater by
  velvet_vcgen [pickGreater] with finish

/-- Extraction evaluates the choice constructively using `findNat`: `10 + 200 = 210` -> `some 211`. -/
example : (pickGreater 10).run = some 211 := by native_decide

/-- Demonic choice combined with `MonadNonDet.assume`. -/
method pickDemonicWithAssume (n : Nat) returns (res : Nat) in DemonicT Option
  requires n_pos : n > 0
  signals (_ : Unit) => False
  ensures res ≥ n
do
  let (x : Nat) :| x ≥ n
  MonadNonDet.assume (x ≥ n)
  return x

prove_correct pickDemonicWithAssume by
  velvet_vcgen [pickDemonicWithAssume] with finish

/-- Extraction evaluates to `some 7`. -/
example : (pickDemonicWithAssume 7).run = some 7 := by native_decide

/- ============================================================================
   2. Loops in Demonic Non-Determinism (`DemonicT Option`)
   ============================================================================ -/

/-- A `while'` loop executing within `DemonicT Option`.
All 6 verification conditions (invariant initialization, preservation, termination metric,
and postcondition) are discharged automatically by `velvet_vcgen`. -/
method loopDemonic (n : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res = n
do
  let mut i : Nat := 0
  while' loop_cond : i < n
    invariant inv_i : i ≤ n
    decreasing by_rem : n - i
    done_with h_done : i = n
  do
    i := i + 1
  return i

prove_correct loopDemonic by
  velvet_vcgen [loopDemonic] with finish

/-- Extraction evaluates the loop to `some 5`. -/
example : (loopDemonic 5).run = some 5 := by native_decide

/-- A loop with non-deterministic choice inside the loop body. -/
method loopWithChoice (n : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res ≥ n
do
  let mut i : Nat := 0
  while' loop_cond : i < n
    invariant inv_i : i ≤ n
    decreasing by_rem : n - i
    done_with h_done : i = n
  do
    let (step : Nat) :| step = 1
    i := i + step
  return i

prove_correct loopWithChoice by
  velvet_vcgen [loopWithChoice] with finish

/-- Extraction evaluates the non-deterministic loop to `some 10`. -/
example : (loopWithChoice 10).run = some 10 := by native_decide

/- ============================================================================
   3. Angelic Non-Determinism (`AngelicT Option`)
   ============================================================================ -/

/-- An angelic program choosing a boolean witness. -/
method pickAngelic (n : Nat) returns (res : Nat) in AngelicT Option
  signals (_ : Unit) => False
  ensures res > n
do
  let (b : Bool) :| b = true
  return n + 1

prove_correct pickAngelic by
  velvet_vcgen [pickAngelic] with try finish

/-- Extraction evaluates to `some 11`. -/
example : (pickAngelic 10).run = some 11 := by native_decide

/-- An angelic program choosing a positive natural increment. -/
method pickAngelicChoice (n : Nat) returns (res : Nat) in AngelicT Option
  signals (_ : Unit) => False
  ensures res > n
do
  let (diff : Nat) :| diff > 0
  return n + diff

prove_correct pickAngelicChoice by
  velvet_vcgen [pickAngelicChoice] with try finish
  case diff => exact Nat.zero_lt_one

/-- Extraction evaluates to `some 11`. -/
example : (pickAngelicChoice 10).run = some 11 := by native_decide

/-- A `while'` loop executing within `AngelicT Option` with non-deterministic choice
inside the loop body. -/
method loopAngelic (n : Nat) returns (res : Nat) in AngelicT Option
  signals (_ : Unit) => False
  ensures res = n
do
  let mut i : Nat := 0
  while' loop_cond : i < n
    invariant inv_i : i ≤ n
    decreasing by_rem : n - i
    done_with h_done : i = n
  do
    let (step : Nat) :| step = 1
    i := i + step
  return i

prove_correct loopAngelic by
  velvet_vcgen [loopAngelic] with try finish

/-- Extraction evaluates the angelic loop to `some 5`. -/
example : (loopAngelic 5).run = some 5 := by native_decide

end Velvet.Examples.NonDet
