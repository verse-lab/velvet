import Velvet.Core.FreerMonad.IO.Effect

open Std.WP Lean.Order WPPartial

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

variable {E Err c In Out : Type} {m : Type → Type} {Pred EPred : Type}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [∀ γ, CCPO (m γ)]
  {div_post : (Err → Trace E → Pred) × EPred} {div_pre : (Err → Trace E → Pred) × EPred → Trace E → Pred}
  [WPPartial (IOModelT E Err m) (Trace E → Pred) ((Err → Trace E → Pred) × EPred) div_post div_pre]
  [StreamChannel c In Out Err] [DecidableEq c] [Provide E c]
  {P : Protocol c (StreamOp In Out) (IOEvent In Out Err) Err} [Model c P E]

def read (ch : c) : IOProgT E Err m In := call ch .read

def write (ch : c) (o : Out) : IOProgT E Err m Unit := call ch (.write o)

@[spec]
theorem read_spec (ch : c) {post : In → Trace E → Pred} {epost : (Err → Trace E → Pred) × EPred} :
    Triple (read (E := E) (m := m) ch)
      (fun h => ⌜Named.mk `allow none (P.allow ch (h.traceOf ch) .read)⌝ ⊓
        ((⨅ i, ⌜Named.mk `onReply none (P.onReply ch (h.traceOf ch) .read (.ok i))⌝ ⇨
            ⨅ h', ⌜Named.mk `h_trace none (h' = h.recordFor ch (.read (.ok i)))⌝ ⇨ post i h') ⊓
          ⨅ e, ⌜Named.mk `onReply none (P.onReply ch (h.traceOf ch) .read (.error e))⌝ ⇨
            ⨅ h', ⌜Named.mk `h_trace none (h' = h.recordFor ch (.read (.error e)))⌝ ⇨ epost.1 e h'))
      post epost :=
  call_spec (P := P) ch .read

@[spec]
theorem write_spec (ch : c) (o : Out) {post : Unit → Trace E → Pred}
    {epost : (Err → Trace E → Pred) × EPred} :
    Triple (write (E := E) (m := m) ch o)
      (fun h => ⌜Named.mk `allow none (P.allow ch (h.traceOf ch) (.write o))⌝ ⊓
        ((⌜Named.mk `onReply none (P.onReply ch (h.traceOf ch) (.write o) (.ok ()))⌝ ⇨
            ⨅ h', ⌜Named.mk `h_trace none (h' = h.recordFor ch (.write o (.ok ())))⌝ ⇨ post () h') ⊓
          ⨅ e, ⌜Named.mk `onReply none (P.onReply ch (h.traceOf ch) (.write o) (.error e))⌝ ⇨
            ⨅ h', ⌜Named.mk `h_trace none (h' = h.recordFor ch (.write o (.error e)))⌝ ⇨ epost.1 e h'))
      post epost :=
  Triple.intro fun h => PartialOrder.rel_trans
    (meet_mono PartialOrder.rel_refl (meet_mono (le_iInf _ _ fun _ => PartialOrder.rel_refl) PartialOrder.rel_refl))
    ((call_spec (P := P) (E := E) (m := m) ch (.write o) (post := post) (epost := epost)).le_wp h)

end IOProg
