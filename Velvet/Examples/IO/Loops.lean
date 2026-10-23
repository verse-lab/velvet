import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg
open scoped GhostSyntax

/-! Servers as loops over IO. Each spec states what the server adds to the socket's history since
`h₀`: a server that runs forever is a partial-correctness loop whose `signals True` allows
divergence. `snapshot` records `h₀` for the invariant, and a ghost list of the requests served so
far turns the history into an equation. -/

namespace Velvet.Examples.IO.Loops

/-! ## A calculator server -/

inductive Op where
  | add (a b : Nat)
  | mul (a b : Nat)

def Op.eval : Op → Nat
  | .add a b => a + b
  | .mul a b => a * b

structure Calc where
  fd : Nat
deriving DecidableEq

instance : Channel Calc Op Nat IOErr := ⟨⟩

def calcP : Protocol Op Nat IOErr where
  allow _ _ := True
  onRead _
    | .ok _ => True
    | .error e => e = .eof
  onWrite _ _
    | .ok => True
    | .error _ => False

@[simp, grind =] theorem calcP_allow (h) (o : Nat) : calcP.allow h o = True := rfl
@[simp, grind =] theorem calcP_onRead_ok (h) (q : Op) : calcP.onRead h (.ok q) = True := rfl
@[simp, grind =] theorem calcP_onRead_error (h) (e : IOErr) : calcP.onRead h (.error e) = (e = .eof) := rfl
@[simp, grind =] theorem calcP_onWrite_ok (h) (o : Nat) : calcP.onWrite h o .ok = True := rfl
@[simp, grind =] theorem calcP_onWrite_error (h) (o : Nat) (e : IOErr) :
    calcP.onWrite h o (.error e) = False := rfl

abbrev CalcEv := Calc × IOEvent Op Nat IOErr

instance : Model calcP Calc CalcEv where
  read _ _ := .error .eof
  read_ok _ _ := rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

/-- One request and its answer. -/
@[simp, grind =] def exchange (q : Op) : List (IOEvent Op Nat IOErr) := [.read (.ok q), .write q.eval .ok]

/- Answers requests until the client hangs up: the history is a run of exchanges, followed by the
end of input. -/
set_option velvet.semantics.termination "partial" in
method serve (c : Calc) returns (r : Unit) in IOProg CalcEv IOErr
  given (h₀ : Trace CalcEv)
  requires (h : Trace CalcEv) => h = h₀
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
      h.traceOf c = start.reveal.traceOf c ++ served.reveal.flatMap exchange)
  do
    let q ← read c
    write c q.eval
    served *:= served ++ [q]

prove_correct serve by
  velvet_vcgen [serve] with finish

/- Answers exactly `n` requests, unless the client hangs up first. -/
method serveN (c : Calc) (n : Nat) returns (r : Unit) in IOProg CalcEv IOErr
  given (h₀ : Trace CalcEv)
  requires (h : Trace CalcEv) => h = h₀
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
      h.traceOf c = start.reveal.traceOf c ++ served.reveal.flatMap exchange)
    invariant counted : (fun _ : Trace CalcEv => served.reveal.length = i ∧ i ≤ n)
    decreasing remaining : n - i
  do
    let q ← read c
    write c q.eval
    served *:= served ++ [q]
    i := i + 1

prove_correct serveN by
  velvet_vcgen [serveN] with finish

/-! ## A key-value server -/

inductive KVReq where
  | get (k : Nat)
  | put (k v : Nat)

inductive KVResp where
  | value (v : Option Nat)
  | ack

structure KV where
  fd : Nat
deriving DecidableEq

instance : Channel KV KVReq KVResp IOErr := ⟨⟩

def kvP : Protocol KVReq KVResp IOErr where
  allow _ _ := True
  onRead _
    | .ok _ => True
    | .error e => e = .eof
  onWrite _ _
    | .ok => True
    | .error _ => False

@[simp, grind =] theorem kvP_allow (h) (o : KVResp) : kvP.allow h o = True := rfl
@[simp, grind =] theorem kvP_onRead_ok (h) (q : KVReq) : kvP.onRead h (.ok q) = True := rfl
@[simp, grind =] theorem kvP_onRead_error (h) (e : IOErr) : kvP.onRead h (.error e) = (e = .eof) := rfl
@[simp, grind =] theorem kvP_onWrite_ok (h) (o : KVResp) : kvP.onWrite h o .ok = True := rfl
@[simp, grind =] theorem kvP_onWrite_error (h) (o : KVResp) (e : IOErr) :
    kvP.onWrite h o (.error e) = False := rfl

abbrev KVEv := KV × IOEvent KVReq KVResp IOErr

instance : Model kvP KV KVEv where
  read _ _ := .error .eof
  read_ok _ _ := rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

abbrev Store := Nat → Option Nat

def respond (st : Store) : KVReq → KVResp
  | .get k => .value (st k)
  | .put _ _ => .ack

def apply (st : Store) : KVReq → Store
  | .get _ => st
  | .put k v => fun k' => if k' = k then some v else st k'

/-- Serving `qs` from an empty store: the history it produces, and the store after. -/
def serveAll (qs : List KVReq) : List (IOEvent KVReq KVResp IOErr) × Store :=
  qs.foldl (fun (t, st) q => (t ++ [.read (.ok q), .write (respond st q) .ok], apply st q))
    ([], fun _ => none)

@[simp, grind =] theorem serveAll_nil : serveAll [] = ([], fun _ => none) := rfl

@[simp, grind =] theorem serveAll_concat (qs : List KVReq) (q : KVReq) :
    serveAll (qs ++ [q]) =
      ((serveAll qs).1 ++ [.read (.ok q), .write (respond (serveAll qs).2 q) .ok],
        apply (serveAll qs).2 q) := by
  simp [serveAll, List.foldl_append]

/- Every answer is computed from the store that the earlier requests built. -/
set_option velvet.semantics.termination "partial" in
method kvServe (c : KV) returns (r : Unit) in IOProg KVEv IOErr
  given (h₀ : Trace KVEv)
  requires (h : Trace KVEv) => h = h₀
  signals (e : IOErr) (h : Trace KVEv) =>
    e = .eof ∧ ∃ qs, h.traceOf c = h₀.traceOf c ++ (serveAll qs).1 ++ [.read (.error .eof)]
  signals True
  ensures (h : Trace KVEv) => False
do
  let start ← snapshot
  let mut store : Store := fun _ => none
  let ghost served := ([] : List KVReq)
  while true
    invariant replayed : (fun h : Trace KVEv =>
      h.traceOf c = start.reveal.traceOf c ++ (serveAll served.reveal).1 ∧
        store = (serveAll served.reveal).2)
  do
    let q ← read c
    write c (respond store q)
    store := apply store q
    served *:= served ++ [q]

prove_correct kvServe by
  velvet_vcgen [kvServe] with finish

end Velvet.Examples.IO.Loops
