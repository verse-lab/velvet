import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg

/-! The smallest IO program: one socket, read a request and answer it. The spec states the whole
trace, so nothing else may happen, and `signals False` says the run always returns. A pure model
answers from the requests the clients send, and the proof carries over to running the program. -/

namespace Velvet.Examples.IO.Basic

abbrev SockEvent := Socket × IOEvent Request Response IOErr

instance [Clients] : PureModel Socket reqResp SockEvent where
  call t s o := socketModel s (t.traceOf s) o
  call_ok _ s o := socketModel_ok s _ o

@[simp, grind =] theorem inj_sockEvent (s : Socket) (e) : (Provide.inj s e : SockEvent) = (s, e) := rfl

method reply [Clients] (s : Socket) returns (q : Request) in IOProg SockEvent IOErr
  given (h₀ : Trace SockEvent)
  requires (h : Trace SockEvent) => h = h₀
  signals (e : IOErr) (h : Trace SockEvent) =>
    (e = .eof ∨ e = .reset) ∧
      (h.events = h₀.events ++ [(s, .read (.error e))] ∨
        ∃ q : Request, h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.error e))])
  signals False
  ensures (h : Trace SockEvent) => h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.ok ()))]
do
  let q ← read s
  write s (Response.mk q.id)
  return q

prove_correct reply by
  velvet_vcgen [reply] with finish

/-- What the proof gives a run: it returns, and either both steps happened or the socket failed. -/
theorem reply_run [Clients] (s : Socket) (h₀ : Trace SockEvent) :
    match ((reply s).interp (m := IOModel SockEvent IOErr)).run.run h₀ with
    | some (.ok q, h) => h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.ok ()))]
    | some (.error e, _) => e = .eof ∨ e = .reset
    | none => False := by
  have := (IOModelT.refines (reply.spec s h₀)).le_wp h₀ (by simp [Named.mk_eq])
  simp only [ExceptT.wp_apply_eq, StateT.wp_apply_eq] at this
  revert this
  generalize ((reply s).interp (m := IOModel SockEvent IOErr)).run.run h₀ = r
  rcases r with _ | ⟨_ | q, h⟩ <;> intro this <;> simp only [Named.mk_eq, ofProp_prop_eq] at this
  · exact this
  · exact this.1
  · exact this

end Velvet.Examples.IO.Basic
