import Velvet

/-
# Automatic `ExceptT` inference

Without an `in <MonadStack>` override, each `signals` clause must have exactly one
explicit binder; its type becomes an `ExceptT` layer wrapped around the base `Option`
monad. The base `Option` failure postcondition is the innermost signal, defaulting to
`False`/`True` according to the termination semantics.

-/
open Std.WP

/- One signal, returning `Nat`: `ExceptT String Option Nat`. -/
method maybeFail (b : Bool) returns (res : Nat)
  requires True
  signals boom : (e : String) => e = "boom"
  ensures res = 0
do
  if b then
    throw "boom"
  return 0

/-- info: maybeFail (b : Bool) : ExceptT String Option Nat -/
#guard_msgs in
#check maybeFail

prove_correct maybeFail by
  velvet_vcgen [maybeFail] with finish

/- One signal, returning `String`: `ExceptT String Option String`. -/
method maybeFailString (b : Bool) returns (res : String)
  requires True
  signals boom : (e : String) => e = "boom"
  ensures res = "ok"
do
  if b then
    throw "boom"
  return "ok"

/-- info: maybeFailString (b : Bool) : ExceptT String Option String -/
#guard_msgs in
#check maybeFailString

prove_correct maybeFailString by
  velvet_vcgen [maybeFailString] with finish

/- Two signals, returning `Int`: `ExceptT String (ExceptT Nat Option) Int`. -/
method twoChannelsInt returns (res : Int)
  requires True
  signals str : (e : String) => e = "s"
  signals nat : (e : Nat) => e = 3
  ensures res = 0
do
  return 0

/-- info: twoChannelsInt : ExceptT String (ExceptT Nat Option) Int -/
#guard_msgs in
#check twoChannelsInt

prove_correct twoChannelsInt by
  velvet_vcgen [twoChannelsInt] with finish

/- Three signals, returning a product:
`ExceptT String (ExceptT Int (ExceptT Bool Option)) (Nat × String)`. -/
method threeChannelsProd returns (res : Nat × String)
  requires True
  signals str : (e : String) => e = "s"
  signals int : (e : Int) => e = 3
  signals bool : (e : Bool) => e = true
  ensures res = (0, "ok")
do
  return (0, "ok")

/-- info: threeChannelsProd : ExceptT String (ExceptT Int (ExceptT Bool Option)) (Nat × String) -/
#guard_msgs in
#check threeChannelsProd

prove_correct threeChannelsProd by
  velvet_vcgen [threeChannelsProd] with finish
