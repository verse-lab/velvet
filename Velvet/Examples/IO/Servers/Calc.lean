import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg
open scoped GhostSyntax

/-! A calculator server, as a loop over IO. Each spec states what the server adds to the socket's history since
`h₀`: a server that runs forever is a partial-correctness loop whose `signals True` allows
divergence. `snapshot` records `h₀` for the invariant, and a ghost list of the requests served so
far turns the history into an equation. The protocols only let a server answer the pending request,
and only with the right answer, so they constrain every step of runs that never end as well. -/

namespace Velvet.Examples.IO.Servers.Calc

inductive Op where
  | add (a b : Nat)
  | mul (a b : Nat)

def Op.eval : Op → Nat
  | .add a b => a + b
  | .mul a b => a * b

structure Calc where
  fd : Nat
deriving DecidableEq

instance : StreamChannel Calc Op Nat IOErr := ⟨⟩

/-- The request read but not yet answered. -/
def calcPending (h : List (IOEvent Op Nat IOErr)) : Option Op :=
  h.foldl (fun _ e => match e with | .read (.ok q) => some q | _ => none) none

def calcP : StreamProtocol Calc Op Nat IOErr where
  allow _ h o := match o with
    | .read => calcPending h = none
    | .write r => ∃ q, calcPending h = some q ∧ r = q.eval
  onReply _ _ o r := match o, r with
    | .read, .ok _ => True
    | .read, .error e => e = .eof
    | .write _, .ok _ => True
    | .write _, .error _ => False

@[simp, grind =] theorem calcP_allow_read (ch h) : calcP.allow ch h .read = (calcPending h = none) := rfl
@[simp, grind =] theorem calcP_allow_write (ch h) (r : Nat) :
    calcP.allow ch h (.write r) = ∃ q, calcPending h = some q ∧ r = q.eval := rfl

@[simp, grind =] theorem calcPending_read_ok (h) (q : Op) : calcPending (h ++ [.read (.ok q)]) = some q := by
  simp [calcPending, List.foldl_append]
@[simp, grind =] theorem calcPending_read_error (h) (e : IOErr) : calcPending (h ++ [.read (.error e)]) = none := by
  simp [calcPending, List.foldl_append]
@[simp, grind =] theorem calcPending_write (h) (r : Nat) (u : Except IOErr Unit) :
    calcPending (h ++ [.write r u]) = none := by
  simp [calcPending, List.foldl_append]

@[simp, grind =] theorem calcP_onReply_read_ok (ch h) (q : Op) : calcP.onReply ch h .read (.ok q) = True := rfl
@[simp, grind =] theorem calcP_onReply_read_error (ch h) (e : IOErr) :
    calcP.onReply ch h .read (.error e) = (e = .eof) := rfl
@[simp, grind =] theorem calcP_onReply_write_ok (ch h) (o : Nat) (u : Unit) :
    calcP.onReply ch h (.write o) (.ok u) = True := rfl
@[simp, grind =] theorem calcP_onReply_write_error (ch h) (o : Nat) (e : IOErr) :
    calcP.onReply ch h (.write o) (.error e) = False := rfl

abbrev CalcEv := Calc × IOEvent Op Nat IOErr

/-- What each calculator client sends. -/
class CalcClients where
  ops : Calc → List Op

/-- A calculator connection delivers its client's requests in order, then the end of input. -/
def calcModel [CalcClients] (c : Calc) (h : List (IOEvent Op Nat IOErr)) : StreamOp Op Nat α → Except IOErr α
  | .read => nextInput (CalcClients.ops c) h
  | .write _ => .ok ()

instance [CalcClients] : PureModel Calc calcP CalcEv where
  call t c o := calcModel c (t.traceOf c) o
  call_ok t c o := by
    cases o with
    | read =>
      simp only [calcModel, nextInput]
      split <;> first | trivial | rfl
    | write _ => trivial

/-- One request and its answer. -/
@[simp, grind =] def exchange (q : Op) : List (IOEvent Op Nat IOErr) := [.read (.ok q), .write q.eval (.ok ())]

/- Answers requests until the client hangs up: the history is a run of exchanges, followed by the
end of input. -/
set_option velvet.semantics.termination "partial" in
method serve [CalcClients] (c : Calc) returns (r : Unit) in IOProg CalcEv IOErr
  given (h₀ : Trace CalcEv)
  requires (h : Trace CalcEv) => h = h₀ ∧ calcPending (h.traceOf c) = none
  signals (e : IOErr) (h : Trace CalcEv) =>
    e = .eof ∧ ∃ qs : List Op,
      h.traceOf c = h₀.traceOf c ++ qs.flatMap exchange ++ [.read (.error .eof)]
  signals True
  ensures (h : Trace CalcEv) => False
do
  let start ← snapshot
  let ghost served := ([] : List Op)
  while true
    invariant answered : (fun h : Trace CalcEv =>
      h.traceOf c = start.reveal.traceOf c ++ served.reveal.flatMap exchange ∧
        calcPending (h.traceOf c) = none)
  do
    let q ← read c
    write c q.eval
    served *:= served ++ [q]

prove_correct serve by
  velvet_vcgen [serve] with finish

/- Answers exactly `n` requests, unless the client hangs up first. -/
method serveN [CalcClients] (c : Calc) (n : Nat) returns (r : Unit) in IOProg CalcEv IOErr
  given (h₀ : Trace CalcEv)
  requires (h : Trace CalcEv) => h = h₀ ∧ calcPending (h.traceOf c) = none
  signals (e : IOErr) (h : Trace CalcEv) =>
    e = .eof ∧ ∃ qs : List Op, qs.length < n ∧
      h.traceOf c = h₀.traceOf c ++ qs.flatMap exchange ++ [.read (.error .eof)]
  signals False
  ensures (h : Trace CalcEv) =>
    ∃ qs : List Op, qs.length = n ∧ h.traceOf c = h₀.traceOf c ++ qs.flatMap exchange
do
  let start ← snapshot
  let mut i := 0
  let ghost served := ([] : List Op)
  while i < n
    invariant answered : (fun h : Trace CalcEv =>
      h.traceOf c = start.reveal.traceOf c ++ served.reveal.flatMap exchange ∧
        calcPending (h.traceOf c) = none)
    invariant counted : (fun _ : Trace CalcEv => served.reveal.length = i ∧ i ≤ n)
    decreasing remaining : n - i
  do
    let q ← read c
    write c q.eval
    served *:= served ++ [q]
    i := i + 1

prove_correct serveN by
  velvet_vcgen [serveN] with finish

end Velvet.Examples.IO.Servers.Calc
