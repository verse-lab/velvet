# Loop exits in other verifiers

How other verifiers treat `break`, `continue` and `return` inside loops, with sources. This is
background for how Velvet's loops handle early exits (see `Velvet/Examples/LoopControl.lean`).

## Summary

| | `break` | `continue` | `return` | Code after the loop sees |
|---|---|---|---|---|
| Dafny | jump to after the loop; invariant not checked | invariant and `decreases` checked | `ensures` checked at the `return` | `inv ∧ ¬guard`, or the exact state at a `break` |
| Viper | no `break` in the language; front ends lower it to `goto` | same, via `goto` | no `return`; lowered to `goto` the method end | whatever reaches the label, as in Dafny |
| Why3 | local exception; its postcondition is the code after the loop | local exception | exception caught at the function; postcondition is the function's | `inv ∧ ¬guard`, or the exception's state |
| Lean `vcgen` | exit invariant `inv true s` proved at the `break` | `inv false s` | stored in the return slot; proves `inv true s` like a `break` | only `inv true s` |
| Velvet, no `done_with` | goes to the code after the loop with the facts at the `break` | invariant and measure | `ensures` checked at the `return` | `inv ∧ ¬cond`, or the exact state at a `break` |
| Velvet, `done_with D` | invariants and `D` proved at the `break` | invariant and measure | `ensures` checked at the `return` | only the invariants and `D` |

## Dafny

Checked locally with `dafny verify`:

- At a `break`, the loop invariant is not checked.
- After the loop, the program is verified in either the normal-exit state (`inv ∧ ¬guard`) or the
  exact state at a `break`, with all facts known there.
- A `return` inside a loop is checked against `ensures` at the `return`.

Dafny compiles to Boogie, where `break` is a jump to a label after the loop. Boogie generates
verification conditions for unstructured programs in a way that shares the code after a join
point, so the code after the loop is verified once no matter how many paths reach it:

- M. Barnett, K. R. M. Leino. *Weakest-precondition of unstructured programs.* PASTE 2005.
- C. Flanagan, J. B. Saxe. *Avoiding exponential explosion: generating compact verification
  conditions.* POPL 2001.

## Viper

Viper has `while` loops, `goto` and labels, but no `break`, `continue` or `return`. A label may
carry invariants, and loops are found as back-edges in the control-flow graph. Front ends (Prusti,
Gobra, Nagini) lower early exits to jumps. I did not find documentation of each front end's exact
encoding; this is the standard lowering.

- [Viper tutorial](https://viper.ethz.ch/tutorial/)
- [Silver issue #296: invariants on labels should be disallowed unless they form loop heads](https://github.com/viperproject/silver/issues/296)
- [Silicon issue #392: AST-to-CFG transformation and irreducible CFGs](https://github.com/viperproject/silicon/issues/392)

## Why3

`break`, `continue` and `return` are sugar for local exceptions ("labels as exceptions"). The WP of
an expression takes one postcondition per exception, and a handler's postcondition is the WP of
the handler's code. The loop rule only constrains the normal outcome; exception postconditions
pass through it. So a `break` must establish what the code after the loop needs, and a `return`
must establish the function's postcondition, without any summary from the user.

- [Why3 `expr.ml`: labels used as exceptions for break, continue and return](https://gitlab.inria.fr/why3/why3/blob/cda6d915982714f3e6437b72798463a618d0bc85/src/mlw/expr.ml)
- [Why3 syntax reference: `break`, `continue`, `try`/`raise`](https://www.why3.org/doc/syntaxref.html)
- [Why3 merge request 649: `while true` loops exited using local exceptions](https://gitlab.inria.fr/why3/why3/-/merge_requests/649)

## Abrupt termination in general

- [S. Schlager, KeY Symposium 2005: loop invariant rules with `break`, `continue`, exceptions and
  `return` in Java](https://formal.kastel.kit.edu/key/keysymposium05/slides/Steffen_Schlager.pdf)
