import Velvet.Core.FreerMonad.WP

/-- A channel kind `c`: a request `o : op α` is answered with an `α` or an `Err`, and the call is
recorded in the channel's history as an `Ev`. -/
class Channel (c : Type) (op : outParam (Type → Type)) (Ev Err : outParam Type) where
  log : ∀ {α : Type}, op α → Except Err α → Ev

/-- What may be asked of channel `ch` given its history, and what it may answer. -/
structure Protocol (c : Type) (op : Type → Type) (Ev Err : Type) where
  allow : ∀ {α : Type}, c → List Ev → op α → Prop
  onReply : ∀ {α : Type}, c → List Ev → op α → Except Err α → Prop
