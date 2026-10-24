import Velvet.Core.FreerMonad.IO.Channel

/-- The event type `E` provides channel kind `c`: it holds `c`'s events, so a program over traces of
`E` can use channels of kind `c`. -/
class Provide (E c : Type) {op : outParam (Type → Type)} {Ev Err : outParam Type} [Channel c op Ev Err] where
  inj : c → Ev → E
  proj : E → Option (c × Ev)
  proj_inj : ∀ ch e, proj (inj ch e) = some (ch, e)

/-- An event of channel kind `c`, held in `E`, is never taken for one of kind `c'`. -/
class Distinguish (E c c' : Type) {op : outParam (Type → Type)} {Ev Err : outParam Type}
    {op' : outParam (Type → Type)} {Ev' Err' : outParam Type}
    [Channel c op Ev Err] [Channel c' op' Ev' Err'] [Provide E c] [Provide E c'] : Prop where
  distinguish : ∀ (ch : c) e, Provide.proj (c := c') (Provide.inj ch e : E) = none

instance instProvideProd {c Ev Err : Type} {op : Type → Type} [Channel c op Ev Err] : Provide (c × Ev) c where
  inj ch e := (ch, e)
  proj x := some x
  proj_inj _ _ := rfl

instance instProvideSumRight {c Ev Err A B : Type} {op : Type → Type} [Channel c op Ev Err] [Provide B c] :
    Provide (A ⊕ B) c where
  inj ch e := .inr (Provide.inj ch e)
  proj
    | .inr x => Provide.proj x
    | .inl _ => none
  proj_inj _ _ := by simp [Provide.proj_inj]

instance instProvideSumLeft {c Ev Err A B : Type} {op : Type → Type} [Channel c op Ev Err] [Provide A c] :
    Provide (A ⊕ B) c where
  inj ch e := .inl (Provide.inj ch e)
  proj
    | .inl x => Provide.proj x
    | .inr _ => none
  proj_inj _ _ := by simp [Provide.proj_inj]

section Sum
variable {c c' Ev Err Ev' Err' A B : Type} {op op' : Type → Type}
  [Channel c op Ev Err] [Channel c' op' Ev' Err']

instance [Provide A c] [Provide B c'] :
    @Distinguish (A ⊕ B) c c' op Ev Err op' Ev' Err' _ _ instProvideSumLeft instProvideSumRight :=
  ⟨fun _ _ => rfl⟩

instance [Provide B c] [Provide A c'] :
    @Distinguish (A ⊕ B) c c' op Ev Err op' Ev' Err' _ _ instProvideSumRight instProvideSumLeft :=
  ⟨fun _ _ => rfl⟩

instance [Provide A c] [Provide A c'] [Distinguish A c c'] :
    @Distinguish (A ⊕ B) c c' op Ev Err op' Ev' Err' _ _ instProvideSumLeft instProvideSumLeft :=
  ⟨fun ch e => by simp [Provide.proj, Provide.inj, Distinguish.distinguish]⟩

instance [Provide B c] [Provide B c'] [Distinguish B c c'] :
    @Distinguish (A ⊕ B) c c' op Ev Err op' Ev' Err' _ _ instProvideSumRight instProvideSumRight :=
  ⟨fun ch e => by simp [Provide.proj, Provide.inj, Distinguish.distinguish]⟩

end Sum

structure Trace (E : Type) where
  events : List E

namespace Trace
variable {E c Ev Err : Type} {op : Type → Type} [Channel c op Ev Err] [DecidableEq c] [Provide E c]

def Provide.on (ch : c) (x : E) : Option Ev :=
  (Provide.proj x).bind fun (ch', e) => if ch' = ch then some e else none

def traceOf (t : Trace E) (ch : c) : List Ev := t.events.filterMap (Provide.on ch)

def recordFor (t : Trace E) (ch : c) (e : Ev) : Trace E := ⟨t.events ++ [Provide.inj ch e]⟩

omit [DecidableEq c] in
@[simp, grind =]
theorem mem_recordFor (x : E) (t : Trace E) (ch : c) (e : Ev) :
    x ∈ (t.recordFor ch e).events ↔ x ∈ t.events ∨ x = Provide.inj ch e := by
  simp [recordFor]

omit [DecidableEq c] in
@[simp, grind =]
theorem events_recordFor (t : Trace E) (ch : c) (e : Ev) :
    (t.recordFor ch e).events = t.events ++ [Provide.inj ch e] := rfl

omit [DecidableEq c] in
@[simp, grind =]
theorem getLast?_recordFor (t : Trace E) (ch : c) (e : Ev) :
    (t.recordFor ch e).events.getLast? = some (Provide.inj ch e) := by
  simp [recordFor]

@[simp, grind =]
theorem traceOf_recordFor_self (t : Trace E) (ch : c) (e : Ev) :
    (t.recordFor ch e).traceOf ch = t.traceOf ch ++ [e] := by
  simp [traceOf, recordFor, Provide.on, List.filterMap_append, Provide.proj_inj]

@[simp, grind =]
theorem traceOf_recordFor_ne (t : Trace E) {ch ch' : c} (hne : ch ≠ ch') (e : Ev) :
    (t.recordFor ch' e).traceOf ch = t.traceOf ch := by
  simp [traceOf, recordFor, Provide.on, List.filterMap_append, Provide.proj_inj, Ne.symm hne]

variable {c' Ev' Err' : Type} {op' : Type → Type} [Channel c' op' Ev' Err'] [Provide E c']

@[simp, grind =]
theorem traceOf_recordFor_other [Distinguish E c' c] (t : Trace E) (ch : c) (ch' : c') (e : Ev') :
    (t.recordFor ch' e).traceOf ch = t.traceOf ch := by
  simp [traceOf, recordFor, Provide.on, List.filterMap_append, Distinguish.distinguish]

end Trace
