module

public import Velvet
public meta import Velvet

open Std.WP
open scoped GhostSyntax

/-!
# Ghost reads in a `decreasing` measure

A `while` measure is only used in proofs, so it may read ghost variables, and the method still
compiles and runs.
-/

namespace Velvet.Examples.Regressions.GhostMeasure

method tickWithGhost returns (res : Nat)
  ensures res = 10
do
  let mut i := 0
  let ghost ctr := 0
  while loop_cond: i < 10
    invariant ghost_ctr: ctr.reveal = i ∧ i ≤ 10
    decreasing rem: 10 - ctr.reveal
  do
    i := i + 1
    ctr *:= ctr + 1
  return i

prove_correct tickWithGhost by
  velvet_vcgen [tickWithGhost] with finish

/-- info: some 10 -/
#guard_msgs in
#eval tickWithGhost

method findWithGhost (n : Nat) returns (res : Nat)
  ensures res ≤ n
do
  let mut i := 0
  let ghost ctr := 0
  while loop_cond: i < n
    invariant ghost_ctr: ctr.reveal = i ∧ i ≤ n
    decreasing rem: n - ctr.reveal
  do
    if i = 3 then return i
    i := i + 1
    ctr *:= ctr + 1
  return i

prove_correct findWithGhost by
  velvet_vcgen [findWithGhost] with finish

/-- info: some 3 -/
#guard_msgs in
#eval findWithGhost 5

end Velvet.Examples.Regressions.GhostMeasure
