module

public import Velvet
public meta import Velvet

open Std.WP

namespace Velvet.Examples.SplitProdBinder

/-
Splitting a product binder `∀ p : α × β, P p` into `∀ a b, P (a, b)` must build maximally shared
terms, which `sym.debug` checks.
-/
set_option sym.debug true

/-- The smallest goal that reaches `splitProdBinder`: a leading binder over a product. -/
example : ∀ p : Nat × Nat, Triple (pure p.1 : Id Nat) True (fun r => r = p.1) estack⟨⟩ := by
  velvet_vcgen

/-- Loop state tuples reach it the same way, e.g. a `while` loop with two mutable variables. -/
method sumPairs (n : Nat) returns (res : Nat)
  ensures res = n
do
  let mut i := 0
  let mut acc := 0
  while i < n
    invariant bound : i ≤ n
    invariant tracks : acc = i
    decreasing n - i
  do
    i := i + 1
    acc := acc + 1
  return acc

prove_correct sumPairs by
  velvet_vcgen [sumPairs] with finish

end Velvet.Examples.SplitProdBinder
