module

public import Velvet
public meta import Velvet

open Std.Internal.Do

/-
# Automatic `ExceptT` inference

Without an `in <MonadStack>` override, a typed `signals` binder adds an `ExceptT`
layer around the base `Option` monad. An optional final binderless clause describes
Option failure directly; otherwise it defaults to `False`/`True` according to the
termination semantics.

-/

/- A binderless signal specifies Option failure without adding an ExceptT layer. -/
method noFailure (n : Nat) returns (res : Nat)
  signals cannot_fail : False
  ensures res = n
do
  return n

/-- info: noFailure (n : Nat) : Option Nat -/
#guard_msgs in
#check noFailure

prove_correct noFailure by
  velvet_vcgen [noFailure] with finish

/- A final binderless signal supplies the base Option contract of an inferred stack. -/
method maybeFailWithBaseSignal (b : Bool) returns (res : Nat)
  signals boom : (e : String) => e = "boom"
  signals allowed_failure : True
  ensures res = 0
do
  if b then throw "boom"
  return 0

/-- info: maybeFailWithBaseSignal (b : Bool) : ExceptT String Option Nat -/
#guard_msgs in
#check maybeFailWithBaseSignal

prove_correct maybeFailWithBaseSignal by
  velvet_vcgen [maybeFailWithBaseSignal] with finish

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
