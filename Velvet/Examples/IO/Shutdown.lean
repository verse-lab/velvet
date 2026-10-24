import Velvet.Examples.IO.Loops

open Std.WP Lean.Order IOProg
open scoped GhostSyntax
open Velvet.Examples.IO Velvet.Examples.IO.Loops

/-! A server that stops on one request, `quit`. The `ensures` describes the history when it stops;
`allowRead` and `allowWrite` are checked at every step of every run, including runs that never
stop, so a server that answers nothing, or answers wrongly, fails at its first bad step. -/

namespace Velvet.Examples.IO.Shutdown

inductive Req where
  | op (o : Op)
  | quit

structure Conn where
  fd : Nat
deriving DecidableEq

instance : Channel Conn Req Nat IOErr := ⟨⟩

/-- Whether the client has asked to stop. -/
def quitted (h : List (IOEvent Req Nat IOErr)) : Bool :=
  h.foldl (fun b e => match e with | .read (.ok .quit) => true | _ => b) false

/-- The request awaiting an answer. -/
def awaiting (h : List (IOEvent Req Nat IOErr)) : Option Op :=
  h.foldl (fun _ e => match e with | .read (.ok (.op o)) => some o | _ => none) none

def connP : Protocol Req Nat IOErr where
  allowRead h := quitted h = false
  allowWrite h r := ∃ o, awaiting h = some o ∧ r = o.eval
  onRead _
    | .ok _ => True
    | .error e => e = .eof
  onWrite _ _
    | .ok => True
    | .error _ => False

@[simp, grind =] theorem connP_allowRead (h) : connP.allowRead h = (quitted h = false) := rfl
@[simp, grind =] theorem connP_allowWrite (h) (r : Nat) :
    connP.allowWrite h r = ∃ o, awaiting h = some o ∧ r = o.eval := rfl
@[simp, grind =] theorem connP_onRead_ok (h) (q : Req) : connP.onRead h (.ok q) = True := rfl
@[simp, grind =] theorem connP_onRead_error (h) (e : IOErr) : connP.onRead h (.error e) = (e = .eof) := rfl
@[simp, grind =] theorem connP_onWrite_ok (h) (r : Nat) : connP.onWrite h r .ok = True := rfl
@[simp, grind =] theorem connP_onWrite_error (h) (r : Nat) (e : IOErr) :
    connP.onWrite h r (.error e) = False := rfl

@[simp, grind =] theorem quitted_quit (h) : quitted (h ++ [.read (.ok .quit)]) = true := by
  simp [quitted, List.foldl_append]
@[simp, grind =] theorem quitted_op (h) (o : Op) : quitted (h ++ [.read (.ok (.op o))]) = quitted h := by
  simp [quitted, List.foldl_append]
@[simp, grind =] theorem quitted_error (h) (e : IOErr) : quitted (h ++ [.read (.error e)]) = quitted h := by
  simp [quitted, List.foldl_append]
@[simp, grind =] theorem quitted_write (h) (r : Nat) (w : WriteOutcome IOErr) :
    quitted (h ++ [.write r w]) = quitted h := by
  simp [quitted, List.foldl_append]

@[simp, grind =] theorem awaiting_op (h) (o : Op) : awaiting (h ++ [.read (.ok (.op o))]) = some o := by
  simp [awaiting, List.foldl_append]
@[simp, grind =] theorem awaiting_quit (h) : awaiting (h ++ [.read (.ok .quit)]) = none := by
  simp [awaiting, List.foldl_append]
@[simp, grind =] theorem awaiting_error (h) (e : IOErr) : awaiting (h ++ [.read (.error e)]) = none := by
  simp [awaiting, List.foldl_append]
@[simp, grind =] theorem awaiting_write (h) (r : Nat) (w : WriteOutcome IOErr) :
    awaiting (h ++ [.write r w]) = none := by
  simp [awaiting, List.foldl_append]

abbrev ConnEv := Conn × IOEvent Req Nat IOErr

instance : Model connP Conn ConnEv where
  read _ _ := .error .eof
  read_ok _ _ := rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

/-- One request and its answer. -/
@[simp, grind =] def served (o : Op) : List (IOEvent Req Nat IOErr) := [.read (.ok (.op o)), .write o.eval .ok]

set_option velvet.semantics.termination "partial" in
method serve (c : Conn) returns (r : Unit) in IOProg ConnEv IOErr
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

end Velvet.Examples.IO.Shutdown
