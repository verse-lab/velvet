module

public import Velvet
public meta import Velvet

open Std.WP Lean.Order

namespace Velvet.Examples.SplitAfterClear

/-
`velvet_vcgen` fails to split an `if` program once a hypothesis has been cleared and the goal
split by `constructor`. Each change below makes it work: keeping the hypothesis, or introducing
`n` first. The failing case is pinned, so this file stops building once the bug is fixed.
-/

/--
error: Failed to apply split rule for ⏎
  if n✝ = 0 then pure true
  else do
    let r ← q (n✝ - 1)
    pure !r
-/
#guard_msgs in
example (q : Nat → Option Bool)
    (h : (∀ n, ⦃ ⌜n % 2 = 0⌝ ⦄ q n ⦃ fun r => ⌜r = true⌝; fun _ => ⌜True⌝ ⦄) ∧ True) :
    (∀ n, ⦃ ⌜n % 2 = 1⌝ ⦄ (if n = 0 then pure true else do let r ← q (n - 1); pure !r)
        ⦃ fun r => ⌜r = false⌝; fun _ => ⌜True⌝ ⦄) ∧ True := by
  have h1 := h.1
  clear h
  constructor
  · velvet_vcgen with finish
  · trivial

/-- Without `clear h`, the program is split. -/
example (q : Nat → Option Bool)
    (h : (∀ n, ⦃ ⌜n % 2 = 0⌝ ⦄ q n ⦃ fun r => ⌜r = true⌝; fun _ => ⌜True⌝ ⦄) ∧ True) :
    (∀ n, ⦃ ⌜n % 2 = 1⌝ ⦄ (if n = 0 then pure true else do let r ← q (n - 1); pure !r)
        ⦃ fun r => ⌜r = false⌝; fun _ => ⌜True⌝ ⦄) ∧ True := by
  have h1 := h.1
  constructor
  · velvet_vcgen with finish
  · trivial

/-- With `n` introduced before `velvet_vcgen`, the program is split. -/
example (q : Nat → Option Bool)
    (h : (∀ n, ⦃ ⌜n % 2 = 0⌝ ⦄ q n ⦃ fun r => ⌜r = true⌝; fun _ => ⌜True⌝ ⦄) ∧ True) :
    (∀ n, ⦃ ⌜n % 2 = 1⌝ ⦄ (if n = 0 then pure true else do let r ← q (n - 1); pure !r)
        ⦃ fun r => ⌜r = false⌝; fun _ => ⌜True⌝ ⦄) ∧ True := by
  have h1 := h.1
  clear h
  constructor
  · intro n
    velvet_vcgen with finish
  · trivial

end Velvet.Examples.SplitAfterClear
