import Velvet.Core.FreerMonad.IO.Effect

open Std.WP Lean.Order

/-! Streams: channels that are read from and written to. -/

inductive StreamOp (In Out : Type) : Type → Type where
  | read : StreamOp In Out In
  | write (o : Out) : StreamOp In Out Unit

inductive IOEvent (In Out Err : Type) where
  | read (r : Except Err In)
  | write (o : Out) (r : Except Err Unit)

def StreamOp.log : StreamOp In Out α → Except Err α → IOEvent In Out Err
  | .read, r => .read r
  | .write o, r => .write o r

/-- A channel kind read from with `In`s and written to with `Out`s; its history is `IOEvent`s. -/
class StreamChannel (c : Type) (In Out Err : outParam Type) where

instance [StreamChannel c In Out Err] : Channel c (StreamOp In Out) (IOEvent In Out Err) Err :=
  ⟨StreamOp.log⟩

abbrev StreamProtocol (c In Out Err : Type) := Protocol c (StreamOp In Out) (IOEvent In Out Err) Err

namespace IOProg

variable {E Err c In Out : Type} [StreamChannel c In Out Err] [DecidableEq c] [Provide E c]
  {P : Protocol c (StreamOp In Out) (IOEvent In Out Err) Err} [Model c P E]

def read (ch : c) : IOProg E Err In := call ch .read

def write (ch : c) (o : Out) : IOProg E Err Unit := call ch (.write o)

@[spec]
theorem read_spec (ch : c) {post : In → Trace E → Prop} {epost : (Err → Trace E → Prop) × (Unit → Prop)} :
    Triple (read (E := E) ch)
      ((fun h => Named.mk `allow none (P.allow ch (h.traceOf ch) .read)) ⊓
        ((fun h => ∀ i, Named.mk `onReply none (P.onReply ch (h.traceOf ch) .read (.ok i)) →
            ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (.read (.ok i))) → post i h') ⊓
          fun h => ∀ e, Named.mk `onReply none (P.onReply ch (h.traceOf ch) .read (.error e)) →
            ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (.read (.error e))) → epost.1 e h'))
      post epost :=
  call_spec (P := P) ch .read

@[spec]
theorem write_spec (ch : c) (o : Out) {post : Unit → Trace E → Prop}
    {epost : (Err → Trace E → Prop) × (Unit → Prop)} :
    Triple (write (E := E) ch o)
      ((fun h => Named.mk `allow none (P.allow ch (h.traceOf ch) (.write o))) ⊓
        ((fun h => Named.mk `onReply none (P.onReply ch (h.traceOf ch) (.write o) (.ok ())) →
            ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (.write o (.ok ()))) → post () h') ⊓
          fun h => ∀ e, Named.mk `onReply none (P.onReply ch (h.traceOf ch) (.write o) (.error e)) →
            ∀ h', Named.mk `h_trace none (h' = h.recordFor ch (.write o (.error e))) → epost.1 e h'))
      post epost := by
  apply Triple.intro
  intro h hw
  simp only [meet_apply, meet_prop_eq_and] at hw
  have hc := (call_spec (P := P) (E := E) ch (.write o) (post := post) (epost := epost)).le_wp h
  simp only [meet_apply, meet_prop_eq_and] at hc
  exact hc ⟨hw.1, fun _ hv => hw.2.1 hv, hw.2.2⟩

end IOProg
