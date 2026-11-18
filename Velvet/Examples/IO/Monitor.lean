import Velvet.Examples.IO.Generic

open IOProg
open Velvet.Examples.IO Velvet.Examples.IO.Generic

/-! Running a program in real `IO`, with models that are plain `IO` code and no proofs, each wrapped in
a monitor that stops the run on a reply the protocol does not allow. The program takes its model as a
parameter, so the same program runs with either. -/

namespace Velvet.Examples.IO.Monitor

def serveOne [Model Socket reqResp SockEvent IO] (s : Socket) : IOProgT SockEvent IOErr IO Request := do
  let q ← read s
  write s (Response.mk q.id)
  return q

instance (α : Type) (ch : Socket) (h) (o : StreamOp Request Response α) (r : Except IOErr α) :
    Decidable (reqResp.onReply ch h o r) := by
  cases o <;> cases r <;> simp only [reqResp_onReply_read_ok, reqResp_onReply_write_ok, reqResp_onReply_error] <;>
    infer_instance

/-- Answers every read with request 7, and prints each reply. -/
@[instance_reducible] def honest : Model Socket reqResp SockEvent IO :=
  Model.monitored reqResp fun _ _ o => match o with
    | .read => pure (.ok ⟨7⟩)
    | .write r => do IO.println s!"replying to {r.id}"; pure (.ok ())

/-- Fails reads with `full`, which the protocol only allows for writes. -/
@[instance_reducible] def liar : Model Socket reqResp SockEvent IO :=
  Model.monitored reqResp fun _ _ o => match o with
    | .read => pure (.error .full)
    | .write _ => pure (.ok ())

def run (model : Model Socket reqResp SockEvent IO) : IO String := do
  try
    match ← ((@serveOne model ⟨1⟩).interp (m := IOModelT SockEvent IOErr IO)).run.run ⟨[]⟩ with
    | (.ok q, h) => pure s!"request {q.id}, {h.events.length} events"
    | (.error _, _) => pure "error"
  catch e => pure s!"stopped: {e}"

/--
info: replying to 7
---
info: "request 7, 2 events"
-/
#guard_msgs in
#eval run honest

/-- info: "stopped: protocol violation" -/
#guard_msgs in
#eval run liar

end Velvet.Examples.IO.Monitor
