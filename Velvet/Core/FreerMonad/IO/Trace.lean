import Velvet.Core.FreerMonad.IO.Channel

class Embeds (c : Type) {In Out Err : outParam Type} [Channel c In Out Err] (E : Type) where
  inj : c → IOEvent In Out Err → E
  proj : E → Option (c × IOEvent In Out Err)
  proj_inj : ∀ ch e, proj (inj ch e) = some (ch, e)

class Distinct (c c' : Type) {In Out Err In' Out' Err' : outParam Type}
    [Channel c In Out Err] [Channel c' In' Out' Err'] (E : Type) [Embeds c E] [Embeds c' E] : Prop where
  left : ∀ (ch' : c') e, Embeds.proj (c := c) (Embeds.inj ch' e : E) = none
  right : ∀ (ch : c) e, Embeds.proj (c := c') (Embeds.inj ch e : E) = none

structure Trace (E : Type) where
  events : List E

namespace Trace
variable {E c In Out Err : Type} [Channel c In Out Err] [DecidableEq c] [Embeds c E]

def Embeds.on (ch : c) (x : E) : Option (IOEvent In Out Err) :=
  (Embeds.proj x).bind fun (ch', e) => if ch' = ch then some e else none

def traceOf (t : Trace E) (ch : c) : List (IOEvent In Out Err) := t.events.filterMap (Embeds.on ch)

def recordFor (t : Trace E) (ch : c) (e : IOEvent In Out Err) : Trace E := ⟨t.events ++ [Embeds.inj ch e]⟩

omit [DecidableEq c] in
@[simp, grind =]
theorem mem_recordFor (x : E) (t : Trace E) (ch : c) (e : IOEvent In Out Err) :
    x ∈ (t.recordFor ch e).events ↔ x ∈ t.events ∨ x = Embeds.inj ch e := by
  simp [recordFor]

omit [DecidableEq c] in
@[simp, grind =]
theorem getLast?_recordFor (t : Trace E) (ch : c) (e : IOEvent In Out Err) :
    (t.recordFor ch e).events.getLast? = some (Embeds.inj ch e) := by
  simp [recordFor]

@[simp, grind =]
theorem traceOf_recordFor_self (t : Trace E) (ch : c) (e : IOEvent In Out Err) :
    (t.recordFor ch e).traceOf ch = t.traceOf ch ++ [e] := by
  simp [traceOf, recordFor, Embeds.on, List.filterMap_append, Embeds.proj_inj]

@[simp, grind =]
theorem traceOf_recordFor_ne (t : Trace E) {ch ch' : c} (hne : ch ≠ ch') (e : IOEvent In Out Err) :
    (t.recordFor ch' e).traceOf ch = t.traceOf ch := by
  simp [traceOf, recordFor, Embeds.on, List.filterMap_append, Embeds.proj_inj, Ne.symm hne]

variable {c' In' Out' Err' : Type} [Channel c' In' Out' Err'] [Embeds c' E]

@[simp, grind =]
theorem traceOf_recordFor_other [Distinct c c' E] (t : Trace E) (ch : c) (ch' : c') (e : IOEvent In' Out' Err') :
    (t.recordFor ch' e).traceOf ch = t.traceOf ch := by
  simp [traceOf, recordFor, Embeds.on, List.filterMap_append, Distinct.left]

@[simp, grind =]
theorem traceOf_recordFor_other' [Distinct c' c E] (t : Trace E) (ch : c) (ch' : c') (e : IOEvent In' Out' Err') :
    (t.recordFor ch' e).traceOf ch = t.traceOf ch := by
  simp [traceOf, recordFor, Embeds.on, List.filterMap_append, Distinct.right]

end Trace

class Policy (E : Type) where
  allow : Trace E → Prop

instance (priority := low) Policy.default {E : Type} : Policy E := ⟨fun _ => True⟩

@[simp, grind =]
theorem Policy.allow_default {E : Type} (t : Trace E) : @Policy.allow E Policy.default t = True := rfl

class Model {In Out Err : outParam Type} (P : outParam (Protocol In Out Err)) (c : Type)
    [Channel c In Out Err] (E : Type) [DecidableEq c] [Embeds c E] where
  read : Trace E → c → ReadOutcome In Err
  read_ok : ∀ t ch, P.onRead (t.traceOf ch) (read t ch)
  write : Trace E → c → Out → WriteOutcome Err
  write_ok : ∀ t ch o, P.onWrite (t.traceOf ch) o (write t ch o)
