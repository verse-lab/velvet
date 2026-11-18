import Velvet.Examples.IO.Generic

open Std.WP Lean.Order IOProg
open Velvet.Examples.IO Velvet.Examples.IO.Generic

/-! A program proved once, against the protocol only, with its model as a parameter. Any model can be
plugged in: here, implementations with no proofs, each wrapped in a monitor that stops the run on a
reply the protocol does not allow. -/

namespace Velvet.Examples.IO.Monitor

method serveOne [Model Socket reqResp SockEvent Option] (s : Socket) returns (q : Request)
    in IOProg SockEvent IOErr
  given (h₀ : Trace SockEvent)
  requires (h : Trace SockEvent) => h = h₀ ∧ pending (h.traceOf s) = none
  signals (e : IOErr) (h : Trace SockEvent) =>
    (e = .eof ∨ e = .reset) ∧
      (h.events = h₀.events ++ [(s, .read (.error e))] ∨
        ∃ q : Request, h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.error e))])
  signals True
  ensures (h : Trace SockEvent) => h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.ok ()))]
do
  let q ← read s
  write s (Response.mk q.id)
  return q

prove_correct serveOne by
  velvet_vcgen [serveOne] with finish

/-- What the proof gives a run, with any model: if it returns a request, the trace is one read of it
and one reply to it. -/
theorem serveOne_run (model : Model Socket reqResp SockEvent Option) (s : Socket) (h₀ : Trace SockEvent)
    (hp : pending (h₀.traceOf s) = none) :
    match ((@serveOne model s).interp (m := IOModel SockEvent IOErr)).run.run h₀ with
    | some (.ok q, h) => h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.ok ()))]
    | _ => True := by
  have := (IOModelT.refines (@serveOne.spec model s h₀)).le_wp h₀ (by simp [Named.mk_eq, hp])
  simp only [ExceptT.wp_apply_eq, StateT.wp_apply_eq] at this
  revert this
  generalize ((@serveOne model s).interp (m := IOModel SockEvent IOErr)).run.run h₀ = r
  rcases r with _ | ⟨_ | q, h⟩ <;> intro this <;> try trivial
  simp only [Named.mk_eq, ofProp_prop_eq] at this
  exact this

instance (α : Type) (ch : Socket) (h) (o : StreamOp Request Response α) (r : Except IOErr α) :
    Decidable (reqResp.onReply ch h o r) := by
  cases o <;> cases r <;> simp only [reqResp_onReply_read_ok, reqResp_onReply_write_ok, reqResp_onReply_error] <;>
    infer_instance

/-- Answers every read with request 7. -/
@[instance_reducible] def honest : Model Socket reqResp SockEvent Option :=
  Model.monitored reqResp fun _ _ o => match o with
    | .read => some (.ok ⟨7⟩)
    | .write _ => some (.ok ())

/-- Fails reads with `full`, which the protocol only allows for writes. -/
@[instance_reducible] def liar : Model Socket reqResp SockEvent Option :=
  Model.monitored reqResp fun _ _ o => match o with
    | .read => some (.error .full)
    | .write _ => some (.ok ())

def run (model : Model Socket reqResp SockEvent Option) : String :=
  match ((@serveOne model ⟨1⟩).interp (m := IOModel SockEvent IOErr)).run.run ⟨[]⟩ with
  | some (.ok q, h) => s!"request {q.id}, {h.events.length} events"
  | some (.error _, _) => "error"
  | none => "stopped"

/-- info: "request 7, 2 events" -/
#guard_msgs in
#eval run honest

/-- info: "stopped" -/
#guard_msgs in
#eval run liar

end Velvet.Examples.IO.Monitor
