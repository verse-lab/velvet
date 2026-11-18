import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg
open scoped GhostSyntax

/-! A calculator server, as a loop over IO. A client sends calculations, each answered with its
result, and may send `quit`. Each spec states what the server adds to the socket's history since
`h₀`: `snapshot` records `h₀` for the invariant, and a ghost list of the calculations answered so far
turns the history into an equation. The protocol only lets the server answer the pending
calculation, with the right result, and never read past `quit`, so it constrains every step of runs
that never end as well. -/

namespace Velvet.Examples.IO.Servers.Calc

inductive Op where
  | add (a b : Nat)
  | mul (a b : Nat)

def Op.eval : Op → Nat
  | .add a b => a + b
  | .mul a b => a * b

inductive Req where
  | op (o : Op)
  | quit

structure Calc where
  fd : Nat
deriving DecidableEq

instance : StreamChannel Calc Req Nat IOErr := ⟨⟩

/-- The calculation read but not yet answered. -/
def calcPending (h : List (IOEvent Req Nat IOErr)) : Option Op :=
  h.foldl (fun _ e => match e with | .read (.ok (.op o)) => some o | _ => none) none

/-- Whether the client has sent `quit`. -/
def quitted (h : List (IOEvent Req Nat IOErr)) : Bool :=
  h.foldl (fun b e => match e with | .read (.ok .quit) => true | _ => b) false

def calcP : StreamProtocol Calc Req Nat IOErr where
  allow _ h o := match o with
    | .read => calcPending h = none ∧ quitted h = false
    | .write r => ∃ o, calcPending h = some o ∧ r = o.eval
  onReply _ _ o r := match o, r with
    | .read, .ok _ => True
    | .read, .error e => e = .eof
    | .write _, .ok _ => True
    | .write _, .error _ => False

@[simp, grind =] theorem calcP_allow_read (ch h) :
    calcP.allow ch h .read = (calcPending h = none ∧ quitted h = false) := rfl
@[simp, grind =] theorem calcP_allow_write (ch h) (r : Nat) :
    calcP.allow ch h (.write r) = ∃ o, calcPending h = some o ∧ r = o.eval := rfl

@[simp, grind =] theorem calcP_onReply_read_ok (ch h) (q : Req) : calcP.onReply ch h .read (.ok q) = True := rfl
@[simp, grind =] theorem calcP_onReply_read_error (ch h) (e : IOErr) :
    calcP.onReply ch h .read (.error e) = (e = .eof) := rfl
@[simp, grind =] theorem calcP_onReply_write_ok (ch h) (o : Nat) (u : Unit) :
    calcP.onReply ch h (.write o) (.ok u) = True := rfl
@[simp, grind =] theorem calcP_onReply_write_error (ch h) (o : Nat) (e : IOErr) :
    calcP.onReply ch h (.write o) (.error e) = False := rfl

@[simp, grind =] theorem calcPending_op (h) (o : Op) : calcPending (h ++ [.read (.ok (.op o))]) = some o := by
  simp [calcPending, List.foldl_append]
@[simp, grind =] theorem calcPending_quit (h) : calcPending (h ++ [.read (.ok .quit)]) = none := by
  simp [calcPending, List.foldl_append]
@[simp, grind =] theorem calcPending_read_error (h) (e : IOErr) : calcPending (h ++ [.read (.error e)]) = none := by
  simp [calcPending, List.foldl_append]
@[simp, grind =] theorem calcPending_write (h) (r : Nat) (w : Except IOErr Unit) :
    calcPending (h ++ [.write r w]) = none := by
  simp [calcPending, List.foldl_append]

@[simp, grind =] theorem quitted_quit (h) : quitted (h ++ [.read (.ok .quit)]) = true := by
  simp [quitted, List.foldl_append]
@[simp, grind =] theorem quitted_op (h) (o : Op) : quitted (h ++ [.read (.ok (.op o))]) = quitted h := by
  simp [quitted, List.foldl_append]
@[simp, grind =] theorem quitted_read_error (h) (e : IOErr) : quitted (h ++ [.read (.error e)]) = quitted h := by
  simp [quitted, List.foldl_append]
@[simp, grind =] theorem quitted_write (h) (r : Nat) (w : Except IOErr Unit) :
    quitted (h ++ [.write r w]) = quitted h := by
  simp [quitted, List.foldl_append]

abbrev CalcEv := Calc × IOEvent Req Nat IOErr

/-- What each calculator client sends. -/
class CalcClients where
  requests : Calc → List Req

/-- A calculator connection delivers its client's requests in order, then the end of input. -/
def calcModel [CalcClients] (c : Calc) (h : List (IOEvent Req Nat IOErr)) : StreamOp Req Nat α → Except IOErr α
  | .read => nextInput (CalcClients.requests c) h
  | .write _ => .ok ()

instance [CalcClients] : PureModel Calc calcP CalcEv where
  call t c o := calcModel c (t.traceOf c) o
  call_ok t c o := by
    cases o with
    | read =>
      simp only [calcModel, nextInput]
      split <;> first | trivial | rfl
    | write _ => trivial

/-- One calculation and its answer. -/
@[simp, grind =] def exchange (o : Op) : List (IOEvent Req Nat IOErr) := [.read (.ok (.op o)), .write o.eval (.ok ())]

/- Answers calculations until the client sends `quit` or hangs up. It may run forever, so this is
partial correctness: when it stops on `quit`, the history is a run of exchanges and then `quit`. -/
set_option velvet.semantics.termination "partial" in
method serve [CalcClients] (c : Calc) returns (r : Unit) in IOProg CalcEv IOErr
  given (h₀ : Trace CalcEv)
  requires (h : Trace CalcEv) => h = h₀ ∧ calcPending (h.traceOf c) = none ∧ quitted (h.traceOf c) = false
  signals (e : IOErr) (h : Trace CalcEv) =>
    e = .eof ∧ ∃ os : List Op, h.traceOf c = h₀.traceOf c ++ os.flatMap exchange ++ [.read (.error .eof)]
  signals True
  ensures (h : Trace CalcEv) =>
    ∃ os : List Op, h.traceOf c = h₀.traceOf c ++ os.flatMap exchange ++ [.read (.ok .quit)]
do
  let start ← snapshot
  let ghost served := ([] : List Op)
  while true
    invariant answered : (fun h : Trace CalcEv =>
      h.traceOf c = start.reveal.traceOf c ++ served.reveal.flatMap exchange ∧
        calcPending (h.traceOf c) = none ∧ quitted (h.traceOf c) = false)
  do
    let q ← read c
    match q with
    | .quit => break
    | .op o =>
      write c o.eval
      served *:= served ++ [o]
  return ()

prove_correct serve by
  velvet_vcgen [serve] with finish

/- Answers exactly `n` calculations, unless the client quits or hangs up first; it always stops. -/
method serveN [CalcClients] (c : Calc) (n : Nat) returns (r : Unit) in IOProg CalcEv IOErr
  given (h₀ : Trace CalcEv)
  requires (h : Trace CalcEv) => h = h₀ ∧ calcPending (h.traceOf c) = none ∧ quitted (h.traceOf c) = false
  signals (e : IOErr) (h : Trace CalcEv) =>
    e = .eof ∧ ∃ os : List Op, os.length < n ∧
      h.traceOf c = h₀.traceOf c ++ os.flatMap exchange ++ [.read (.error .eof)]
  signals False
  ensures (h : Trace CalcEv) => ∃ os : List Op,
    (os.length = n ∧ h.traceOf c = h₀.traceOf c ++ os.flatMap exchange) ∨
    (os.length < n ∧ h.traceOf c = h₀.traceOf c ++ os.flatMap exchange ++ [.read (.ok .quit)])
do
  let start ← snapshot
  let mut i := 0
  let ghost served := ([] : List Op)
  while i < n
    invariant answered : (fun h : Trace CalcEv =>
      h.traceOf c = start.reveal.traceOf c ++ served.reveal.flatMap exchange ∧
        calcPending (h.traceOf c) = none ∧ quitted (h.traceOf c) = false)
    invariant counted : (fun _ : Trace CalcEv => served.reveal.length = i ∧ i ≤ n)
    decreasing remaining : n - i
  do
    let q ← read c
    match q with
    | .quit => break
    | .op o =>
      write c o.eval
      served *:= served ++ [o]
      i := i + 1

prove_correct serveN by
  velvet_vcgen [serveN] with finish

end Velvet.Examples.IO.Servers.Calc
