import Velvet.Core.FreerMonad.WP

class Channel (c : Type) (In Out Err : outParam Type) where

inductive ReadOutcome (In Err : Type) where
  | ok (i : In)
  | error (e : Err)

inductive WriteOutcome (Err : Type) where
  | ok
  | error (e : Err)

def ReadOutcome.toExcept : ReadOutcome In Err → Except Err In
  | .ok i => .ok i
  | .error e => .error e

def WriteOutcome.toExcept : WriteOutcome Err → Except Err Unit
  | .ok => .ok ()
  | .error e => .error e

inductive IOEvent (In Out Err : Type) where
  | read (r : ReadOutcome In Err)
  | write (o : Out) (r : WriteOutcome Err)

structure Protocol (In Out Err : Type) where
  allow : List (IOEvent In Out Err) → Out → Prop
  onRead : List (IOEvent In Out Err) → ReadOutcome In Err → Prop
  onWrite : List (IOEvent In Out Err) → Out → WriteOutcome Err → Prop
