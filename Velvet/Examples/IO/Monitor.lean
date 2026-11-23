import Velvet.Examples.IO.Basic

open Std.WP Lean.Order IOProg
open Velvet.Examples.IO Velvet.Examples.IO.Basic

/-! Running a program in real `IO`. The program is proved against the protocol only, with its model
as a parameter. The models here are plain `IO` code with no proofs, each wrapped in a monitor that
stops the run on a reply the protocol does not allow, and the proof still carries over to every run:
if a run returns, its trace is what the spec says. Over `IO` any call may stop, so the spec accepts
every `IO` error. -/

namespace Velvet.Examples.IO.Monitor

method serveOne [Model Socket reqResp SockEvent IO] (s : Socket) returns (q : Request)
    in IOProgT SockEvent IOErr IO
  given (h₀ : Trace SockEvent)
  requires (h : Trace SockEvent) => h = h₀ ∧ pending (h.traceOf s) = none
  signals (e : IOErr) (h : Trace SockEvent) =>
    (e = .eof ∨ e = .reset) ∧
      (h.events = h₀.events ++ [(s, .read (.error e))] ∨
        ∃ q : Request, h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.error e))])
  signals (e : IO.Error) => True
  ensures (h : Trace SockEvent) => h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.ok ()))]
do
  let q ← read s
  write s (Response.mk q.id)
  return q

prove_correct serveOne by
  velvet_vcgen [serveOne] with finish

/-- What the proof gives a real run, with any model and in any state of the world: if it returns a
request, the trace is one read of it and one reply; if the socket fails, the trace is the failed
read, or one read and the failed reply to it; an `IO` error, including the monitor stopping the run,
promises nothing. -/
theorem serveOne_run (model : Model Socket reqResp SockEvent IO) (s : Socket) (h₀ : Trace SockEvent)
    (hp : pending (h₀.traceOf s) = none) (w : Void IO.RealWorld) :
    match ((@serveOne model s).interp (m := IOModelT SockEvent IOErr IO)).run.run h₀ w with
    | .ok (.ok q, h) _ => h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.ok ()))]
    | .ok (.error e, h) _ => (e = .eof ∨ e = .reset) ∧
        (h.events = h₀.events ++ [(s, .read (.error e))] ∨
          ∃ q : Request, h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.error e))])
    | .error _ _ => True := by
  have := (IOModelT.refines (@serveOne.spec model s h₀)).le_wp h₀ (by simp [Named.mk_eq, hp]) w
  revert this
  generalize ((@serveOne model s).interp (m := IOModelT SockEvent IOErr IO)).run.run h₀ w = r
  intro this
  cases r with
  | error => trivial
  | ok p _ =>
    obtain ⟨_ | q, h⟩ := p
    · simpa only [IO.outPost, pushExcept, Named.mk_eq, ofProp_prop_eq] using this
    · simpa only [IO.outPost, pushExcept, Named.mk_eq, ofProp_prop_eq] using this

instance (α : Type) (ch : Socket) (h) (o : StreamOp Request Response α) (r : Except IOErr α) :
    Decidable (reqResp.onReply ch h o r) := by
  cases o <;> cases r <;> simp only [reqResp_onReply_read_ok, reqResp_onReply_write_ok, reqResp_onReply_error] <;>
    infer_instance

/-- Answers every read with request 7, and prints each reply. -/
@[instance_reducible] def honest : Model Socket reqResp SockEvent IO :=
  Model.caught reqResp (fun _ => none) fun _ _ o => match o with
    | .read => pure (.ok ⟨7⟩)
    | .write r => do IO.println s!"replying to {r.id}"; pure (.ok ())

/-- Fails reads with `full`, an error the protocol never allows. -/
@[instance_reducible] def liar : Model Socket reqResp SockEvent IO :=
  Model.caught reqResp (fun _ => none) fun _ _ o => match o with
    | .read => pure (.error .full)
    | .write _ => pure (.ok ())

def run (model : Model Socket reqResp SockEvent IO) : IO String := do
  try
    match ← ((@serveOne model ⟨1⟩).interp (m := IOModelT SockEvent IOErr IO)).run.run ⟨[]⟩ with
    | (.ok q, h) => pure s!"request {q.id}, {h.events.length} events"
    | (.error _, h) => pure s!"error after {h.events.length} events"
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

/-- A socket whose write throws, as real `IO` does on a broken pipe. -/
def brokenPipe : ∀ {α : Type}, Trace SockEvent → Socket → StreamOp Request Response α → IO (Except IOErr α) :=
  fun _ _ o => match o with
    | .read => pure (.ok ⟨7⟩)
    | .write _ => throw (.resourceVanished 32 "broken pipe")

/-- The exceptions the protocol has an error for; the rest are rethrown. -/
def sockError : IO.Error → Option IOErr
  | .resourceVanished .. => some .reset
  | _ => none

/-- info: "stopped: resource vanished (error code: 32, broken pipe)" -/
#guard_msgs in
#eval run (Model.caught reqResp (fun _ => none) brokenPipe)

/-- info: "error after 2 events" -/
#guard_msgs in
#eval run (Model.caught reqResp sockError brokenPipe)

section Pure

local instance : Clients where
  stdin := []
  stdin_ok := by simp
  requests _ := [⟨9⟩]

/-- A pure model, the same one the `Option` examples use, runs the program in `IO` too. -/
@[instance_reducible] def scripted : Model Socket reqResp SockEvent IO := inferInstance

/-- info: "request 9, 2 events" -/
#guard_msgs in
#eval run scripted

end Pure

/-! A server loop over `IO`. Lean takes a diverging `IO` loop to throw some error, so the spec must
accept every `IO` error; it may run forever, so it never claims to return. -/

set_option velvet.semantics.termination "partial" in
method serveAll [Model Socket reqResp SockEvent IO] (s : Socket) returns (n : Nat)
    in IOProgT SockEvent IOErr IO
  requires (h : Trace SockEvent) => pending (h.traceOf s) = none
  signals (e : IOErr) (h : Trace SockEvent) => e = .eof ∨ e = .reset
  signals (e : IO.Error) => True
  ensures (h : Trace SockEvent) => False
do
  let mut n := 0
  while true
    invariant idle : (fun h : Trace SockEvent => pending (h.traceOf s) = none)
  do
    let q ← read s
    write s (Response.mk q.id)
    n := n + 1
  return n

prove_correct serveAll by
  velvet_vcgen [serveAll] with finish

/-- Hands out requests 1, 2 and 3, then the end of input. -/
@[instance_reducible] def three : Model Socket reqResp SockEvent IO :=
  Model.caught reqResp (fun _ => none) fun t s o => match o with
    | .read => let n := (t.traceOf s).length / 2; pure (if n < 3 then .ok ⟨n + 1⟩ else .error .eof)
    | .write r => do IO.println s!"replying to {r.id}"; pure (.ok ())

/--
info: replying to 1
replying to 2
replying to 3
---
info: "hung up after 7 events"
-/
#guard_msgs in
#eval show IO String from do
  let (r, h) ← ((@serveAll three ⟨1⟩).interp (m := IOModelT SockEvent IOErr IO)).run.run ⟨[]⟩
  pure (match r with
    | .error .eof => s!"hung up after {h.events.length} events"
    | _ => "other")

end Velvet.Examples.IO.Monitor
