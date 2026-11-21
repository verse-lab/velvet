module

public import Velvet
public meta import Velvet

open Std.WP

/-!
# `prove_correct` proves the declared contract

`f.spec` has the statement of `f.spec_triple`, elaborated where `f` was declared, even when a
later declaration in `namespace f` shadows a name the contract uses, or the contract uses an `open`
that is no longer in scope.
-/

namespace Velvet.Examples.Regressions.ProveCorrectStatement

public def bound : Nat := 1

method addBound (x : Nat) returns (r : Nat)
  ensures r = x + bound
do
  return x + 1

public def addBound.bound : Nat := 0

prove_correct addBound by
  velvet_vcgen [addBound] with try finish
  all_goals simp [ProveCorrectStatement.bound]

example : addBound.spec_triple := addBound.spec

section
open Nat

method succOf (x : Nat) returns (r : Nat)
  ensures r = succ x
do
  return x + 1

end

prove_correct succOf by
  velvet_vcgen [succOf] with finish

example : succOf.spec_triple := succOf.spec

end Velvet.Examples.Regressions.ProveCorrectStatement
