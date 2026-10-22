import Velvet.Core.FreerMonad.IO.Channel

class Embeds (c : Type) {In Out Err : outParam Type} [Channel c In Out Err] (E : Type) where
  inj : c → IOEvent In Out Err → E
  proj : E → Option (c × IOEvent In Out Err)
  proj_inj : ∀ ch e, proj (inj ch e) = some (ch, e)

class Distinct (c c' : Type) {In Out Err In' Out' Err' : outParam Type}
    [Channel c In Out Err] [Channel c' In' Out' Err'] (E : Type) [Embeds c E] [Embeds c' E] : Prop where
  left : ∀ (ch' : c') e, Embeds.proj (c := c) (Embeds.inj ch' e : E) = none
  right : ∀ (ch : c) e, Embeds.proj (c := c') (Embeds.inj ch e : E) = none

section
variable {E c In Out Err : Type} [Channel c In Out Err] [DecidableEq c] [Embeds c E]

def Embeds.on (ch : c) (x : E) : Option (IOEvent In Out Err) :=
  (Embeds.proj x).bind fun (ch', e) => if ch' = ch then some e else none

def trace (h : List E) (ch : c) : List (IOEvent In Out Err) := h.filterMap (Embeds.on ch)

def record (h : List E) (ch : c) (e : IOEvent In Out Err) : List E := h ++ [Embeds.inj ch e]

@[simp, grind =]
theorem trace_record_self (h : List E) (ch : c) (e : IOEvent In Out Err) :
    trace (record h ch e) ch = trace h ch ++ [e] := by
  simp [trace, record, Embeds.on, List.filterMap_append, Embeds.proj_inj]

@[simp, grind =]
theorem trace_record_ne (h : List E) {ch ch' : c} (hne : ch ≠ ch') (e : IOEvent In Out Err) :
    trace (record h ch' e) ch = trace h ch := by
  simp [trace, record, Embeds.on, List.filterMap_append, Embeds.proj_inj, Ne.symm hne]

variable {c' In' Out' Err' : Type} [Channel c' In' Out' Err'] [Embeds c' E]

@[simp, grind =]
theorem trace_record_other [Distinct c c' E] (h : List E) (ch : c) (ch' : c') (e : IOEvent In' Out' Err') :
    trace (record h ch' e) ch = trace h ch := by
  simp [trace, record, Embeds.on, List.filterMap_append, Distinct.left]

@[simp, grind =]
theorem trace_record_other' [Distinct c' c E] (h : List E) (ch : c) (ch' : c') (e : IOEvent In' Out' Err') :
    trace (record h ch' e) ch = trace h ch := by
  simp [trace, record, Embeds.on, List.filterMap_append, Distinct.right]

end

class Model {In Out Err : outParam Type} (P : outParam (Protocol In Out Err)) (c : Type)
    [Channel c In Out Err] (E : Type) [DecidableEq c] [Embeds c E] where
  read : List E → c → ReadOutcome In Err
  read_ok : ∀ h ch, P.readAssumption (trace h ch) (read h ch)
  write : List E → c → Out → WriteOutcome Err
  write_ok : ∀ h ch o, P.writeAssumption (trace h ch) o (write h ch o)
