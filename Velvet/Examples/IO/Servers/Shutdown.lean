import Velvet.Examples.IO.Servers.Calc

open Std.WP Lean.Order IOProg
open scoped GhostSyntax
open Velvet.Examples.IO Velvet.Examples.IO.Servers.Calc

/-! A server that stops on one request, `quit`. The `ensures` describes the history when it stops;
the protocol's `allow` is checked before every read and write of every run, including runs that never
stop, so a server that answers nothing, or answers wrongly, fails at its first bad step. -/

namespace Velvet.Examples.IO.Servers.Shutdown

inductive Req where
  | op (o : Op)
  | quit

structure Conn where
  fd : Nat
deriving DecidableEq

instance : StreamChannel Conn Req Nat IOErr := ⟨⟩

/-- Whether the client has asked to stop. -/
def quitted (h : List (IOEvent Req Nat IOErr)) : Bool :=
  h.foldl (fun b e => match e with | .read (.ok .quit) => true | _ => b) false

/-- The request awaiting an answer. -/
def awaiting (h : List (IOEvent Req Nat IOErr)) : Option Op :=
  h.foldl (fun _ e => match e with | .read (.ok (.op o)) => some o | _ => none) none

def connP : StreamProtocol Conn Req Nat IOErr where
  allow _ h o := match o with
    | .read => quitted h = false
    | .write r => ∃ o, awaiting h = some o ∧ r = o.eval
  onReply _ _ o r := match o, r with
    | .read, .ok _ => True
    | .read, .error e => e = .eof
    | .write _, .ok _ => True
    | .write _, .error _ => False

@[simp, grind =] theorem connP_allow_read (ch h) : connP.allow ch h .read = (quitted h = false) := rfl
@[simp, grind =] theorem connP_allow_write (ch h) (r : Nat) :
    connP.allow ch h (.write r) = ∃ o, awaiting h = some o ∧ r = o.eval := rfl

@[simp, grind =] theorem connP_onReply_read_ok (ch h) (q : Req) : connP.onReply ch h .read (.ok q) = True := rfl
@[simp, grind =] theorem connP_onReply_read_error (ch h) (e : IOErr) :
    connP.onReply ch h .read (.error e) = (e = .eof) := rfl
@[simp, grind =] theorem connP_onReply_write_ok (ch h) (o : Nat) (u : Unit) :
    connP.onReply ch h (.write o) (.ok u) = True := rfl
@[simp, grind =] theorem connP_onReply_write_error (ch h) (o : Nat) (e : IOErr) :
    connP.onReply ch h (.write o) (.error e) = False := rfl

@[simp, grind =] theorem quitted_quit (h) : quitted (h ++ [.read (.ok .quit)]) = true := by
  simp [quitted, List.foldl_append]
@[simp, grind =] theorem quitted_op (h) (o : Op) : quitted (h ++ [.read (.ok (.op o))]) = quitted h := by
  simp [quitted, List.foldl_append]
@[simp, grind =] theorem quitted_error (h) (e : IOErr) : quitted (h ++ [.read (.error e)]) = quitted h := by
  simp [quitted, List.foldl_append]
@[simp, grind =] theorem quitted_write (h) (r : Nat) (w : Except IOErr Unit) :
    quitted (h ++ [.write r w]) = quitted h := by
  simp [quitted, List.foldl_append]

@[simp, grind =] theorem awaiting_op (h) (o : Op) : awaiting (h ++ [.read (.ok (.op o))]) = some o := by
  simp [awaiting, List.foldl_append]
@[simp, grind =] theorem awaiting_quit (h) : awaiting (h ++ [.read (.ok .quit)]) = none := by
  simp [awaiting, List.foldl_append]
@[simp, grind =] theorem awaiting_error (h) (e : IOErr) : awaiting (h ++ [.read (.error e)]) = none := by
  simp [awaiting, List.foldl_append]
@[simp, grind =] theorem awaiting_write (h) (r : Nat) (w : Except IOErr Unit) :
    awaiting (h ++ [.write r w]) = none := by
  simp [awaiting, List.foldl_append]

abbrev ConnEv := Conn × IOEvent Req Nat IOErr

/-- What each client sends. -/
class ConnClients where
  requests : Conn → List Req

/-- A connection delivers its client's requests in order, then the end of input. -/
def connModel [ConnClients] (c : Conn) (h : List (IOEvent Req Nat IOErr)) : StreamOp Req Nat α → Except IOErr α
  | .read => nextInput (ConnClients.requests c) h
  | .write _ => .ok ()

instance [ConnClients] : Model Conn connP ConnEv where
  call t c o := connModel c (t.traceOf c) o
  call_ok t c o := by
    cases o with
    | read =>
      simp only [connModel, nextInput]
      split <;> first | trivial | rfl
    | write _ => trivial

/-- One request and its answer. -/
@[simp, grind =] def served (o : Op) : List (IOEvent Req Nat IOErr) := [.read (.ok (.op o)), .write o.eval (.ok ())]

set_option velvet.semantics.termination "partial" in
method serve [ConnClients] (c : Conn) returns (r : Unit) in IOProg ConnEv IOErr
  given (h₀ : Trace ConnEv)
  requires (h : Trace ConnEv) => h = h₀ ∧ quitted (h.traceOf c) = false ∧ awaiting (h.traceOf c) = none
  signals (e : IOErr) (h : Trace ConnEv) =>
    e = .eof ∧ ∃ os : List Op, h.traceOf c = h₀.traceOf c ++ os.flatMap served ++ [.read (.error .eof)]
  signals True
  ensures (h : Trace ConnEv) =>
    ∃ os : List Op, h.traceOf c = h₀.traceOf c ++ os.flatMap served ++ [.read (.ok .quit)]
do
  let start ← snapshot
  let ghost done := ([] : List Op)
  while true
    invariant answered : (fun h : Trace ConnEv =>
      h.traceOf c = start.reveal.traceOf c ++ done.reveal.flatMap served ∧
        quitted (h.traceOf c) = false ∧ awaiting (h.traceOf c) = none)
  do
    let r ← read c
    match r with
    | .quit => break
    | .op o =>
      write c o.eval
      done *:= done ++ [o]
  return ()

prove_correct serve by
  velvet_vcgen [serve] with finish

end Velvet.Examples.IO.Servers.Shutdown
