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
4. **Finite Domain Search (`Finitary`)**: Automatic exhaustive search over finite types like `Fin n`.
5. **Non-deterministic Loops**: Loops verified using `while'` with invariants, termination metrics, and `done_with`.
6. **Stateful Non-Determinism**: Embedding stateful effects under `DemonicT (StateT σ Option)`.
7. **Constructive Extraction**: Evaluation of non-deterministic methods via `.run`.
-/

/- ============================================================================
   1. Basic Demonic Choice (`DemonicT Option`)
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

/-- Multiple consecutive non-deterministic choices in sequence. -/
method pickTwoSum (target : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res = target + 5
do
  let (a : Nat) :| a = target
  let (b : Nat) :| b = 5
  return a + b

prove_correct pickTwoSum by
  velvet_vcgen [pickTwoSum] with finish

example : (pickTwoSum 10).run = some 15 := by native_decide

/-- Demonic choice combined with `NonDetT.assume`. -/
method pickDemonicWithAssume (n : Nat) returns (res : Nat) in DemonicT Option
  requires n_pos : n > 0
  signals (_ : Unit) => False
  ensures res ≥ n
do
  let (x : Nat) :| x ≥ n
  NonDetT.assume (x ≥ n)
  return x

prove_correct pickDemonicWithAssume by
  velvet_vcgen [pickDemonicWithAssume] with finish

example : (pickDemonicWithAssume 7).run = some 7 := by native_decide

/-- Conditional non-deterministic choice based on branching control flow. -/
method pickBranch (flag : Bool) (x : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures flag = true → res > x
  ensures flag = false → res = 0
do
  if flag then
    let (y : Nat) :| y > x + 10
    return y
  else
    return 0

prove_correct pickBranch by
  velvet_vcgen [pickBranch] with finish

example : (pickBranch true 5).run = some 16 := by native_decide
example : (pickBranch false 5).run = some 0 := by native_decide

/- ============================================================================
   2. Finite Domain Search (`Finitary`)
   ============================================================================ -/

/-- Finite domain search over `Fin 10`: automatically finds `x` such that `x * x = 16`. -/
method pickSquare (n : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res * res = 16
do
  let (x : Fin 10) :| x.val * x.val = 16
  return x.val

prove_correct pickSquare by
  velvet_vcgen [pickSquare] with finish

example : (pickSquare 0).run = some 4 := by native_decide

/- ============================================================================
   3. Loops in Demonic Non-Determinism (`DemonicT Option`)
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

example : (loopWithChoice 10).run = some 10 := by native_decide

/-- A bounded accumulator loop choosing step sizes ≤ 2 non-deterministically. -/
method loopAccum (n : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res ≤ n * 2
do
  let mut cur : Nat := 0
  let mut i : Nat := 0
  while' loop_cond : i < n
    invariant inv_i : i ≤ n ∧ cur ≤ i * 2
    decreasing by_rem : n - i
    done_with h_done : i = n
  do
    let (step : Nat) :| step ≤ 2
    cur := cur + step
    i := i + 1
  return cur

prove_correct loopAccum by
  velvet_vcgen [loopAccum] with finish

example : (loopAccum 5).run = some 0 := by native_decide

/- ============================================================================
   4. Angelic Non-Determinism (`AngelicT Option`)
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

example : (pickAngelicChoice 10).run = some 11 := by native_decide

/-- Synthesizing a non-trivial factor of 10 angelically. -/
method findDivisor (n : Nat) returns (d : Nat) in AngelicT Option
  signals (_ : Unit) => False
  ensures d > 1 ∧ d < 10 ∧ 10 % d = 0
do
  let (cand : Nat) :| cand > 1 ∧ cand < 10 ∧ 10 % cand = 0
  return cand

prove_correct findDivisor by
  velvet_vcgen [findDivisor] with try finish
  case vc3 => exact 2
  case cand => decide

example : (findDivisor 10).run = some 2 := by native_decide

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

example : (loopAngelic 5).run = some 5 := by native_decide

/- ============================================================================
   5. Stateful Non-Determinism (`DemonicT (StateT σ Option)`)
   ============================================================================ -/

/-- Demonstrates stacking `DemonicT` over `StateT Nat Option`.
Following the ITree / Freer monad approach, base state effects `get` and `set`
are embedded directly into the tree via `.vis` (through `MonadLift`). -/
def incCounter : DemonicT (StateT Nat Option) Nat := do
  let s ← monadLift (get : StateT Nat Option Nat)
  let (step : Nat) :| step ≥ 1
  monadLift (set (s + step) : StateT Nat Option PUnit)
  return s + step

example : (incCounter.run 10) = some (11, 11) := by native_decide

end Velvet.Examples.NonDet
