import Velvet2.Syntax
import Velvet2.VCGen.Frontend

/-!
# Bad VCs — known vcgen_ regressions / infelicities

## Symptom

A `for'` loop lowers to Lean's native annotated `for`, selecting the `done_with`
clause or the current invariant by matching on the unconsumed suffix. For loops
with nontrivial state, vcgen does not split those residual cursor matches before
emitting goals: the targets stay match-shaped with `Named.mk` atoms inside their
branches, and receive generic `vcN` tags instead of the branch's user-facing name.
`finish` therefore leaves `vc1`/`vc3`-style goals open even for simple examples.

Loops over trivial state (`scanRangeVCGen`, `sumDoubleRange`,
`boundedRangeValues` in `Loops.lean`) come out clean and verify with plain
`with finish`.

There is no range-specific loop spec or range automation involved anymore; only
the stdlib `Spec.forInPure` rule and this naming/presentation gap.

## Workarounds

- Rewrite stateful loops as `while'` (see `fibWhile` in `Recursion.lean`) — clean VCs.
- Discharge the residual goals manually after `split`.
- TODO: split generated cursor matches inside VCGen before emission so each
  branch decomposes and gets named normally.
- Unrelated known trap: a bare `match` inside an `ensures` clause breaks assertion
  elaboration ("named loop assertion must return Prop") — wrap such postconditions
  in a named predicate first.
-/

open Std.Internal.Do

-- Minimal repro: TWO mutable variables suffice. With one (`sumDoubleRange`)
-- the VCs come out clean.
method twoVar (n : Nat) returns (r : Nat)
  ensures r_eq: r = n
do
  let mut x := 0
  let mut y := 0
  for' i in List.range n
    invariant xy: x = i ∧ y = i
    done_with d: x = n ∧ y = n
  do
    x := x + 1
    y := y + 1
  return x

@[grind]
def fibAccSpec : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => fibAccSpec n b (a + b)

-- The original offender: three mutable variables. The `while'` rewrite
-- (`fibWhile` in `Recursion.lean`) verifies with plain `with finish`.
method fibFor (n : Nat)
  returns (result : Nat)
  ensures result = fibAccSpec n 0 1
do
  let mut a := 0
  let mut b := 1
  let mut i := 0
  assert hi : i = 0
  for' j in List.range n
    invariant cursor_index : i = j
    invariant fib_values : a = fibAccSpec i 0 1 ∧ b = fibAccSpec i 1 1
    invariant index_bound : i ≤ n
    done_with fib_done : i = n ∧ a = fibAccSpec n 0 1
  do
    let next := a + b
    a := b
    b := next
    i := i + 1
  return a

-- Debug: inspect the leaked goals with `all_goals trace_state`.
prove_correct twoVar by
  vcgen_ [twoVar] with try finish
  all_goals sorry

prove_correct fibFor by
  vcgen_ [fibFor, fibAccSpec] with try finish
  all_goals sorry
