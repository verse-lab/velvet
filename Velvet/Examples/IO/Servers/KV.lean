import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg
open scoped GhostSyntax

/-! A key-value server, as a loop over IO. Every answer is computed from the store that the earlier
requests built, and the protocol only lets the server answer the pending request with that answer. -/

namespace Velvet.Examples.IO.Servers.KV

inductive KVReq where
  | get (k : Nat)
  | put (k v : Nat)

inductive KVResp where
  | value (v : Option Nat)
  | ack

structure KV where
  fd : Nat
deriving DecidableEq

instance : StreamChannel KV KVReq KVResp IOErr := ⟨⟩

abbrev Store := Nat → Option Nat

def respond (st : Store) : KVReq → KVResp
  | .get k => .value (st k)
  | .put _ _ => .ack

def apply (st : Store) : KVReq → Store
  | .get _ => st
  | .put k v => fun k' => if k' = k then some v else st k'

/-- The store after the answered requests, and the request awaiting an answer. -/
def kvState (h : List (IOEvent KVReq KVResp IOErr)) : Store × Option KVReq :=
  h.foldl (fun (st, p) e => match e, p with
    | .read (.ok q), _ => (st, some q)
    | .write _ (.ok _), some q => (apply st q, none)
    | _, _ => (st, none)) (fun _ => none, none)

def kvP : StreamProtocol KV KVReq KVResp IOErr where
  allow _ h o := match o with
    | .read => (kvState h).2 = none
    | .write r => ∃ q, (kvState h).2 = some q ∧ r = respond (kvState h).1 q
  onReply _ _ o r := match o, r with
    | .read, .ok _ => True
    | .read, .error e => e = .eof
    | .write _, .ok _ => True
    | .write _, .error _ => False

@[simp, grind =] theorem kvP_allow_read (ch h) : kvP.allow ch h .read = ((kvState h).2 = none) := rfl
@[simp, grind =] theorem kvP_allow_write (ch h) (r : KVResp) :
    kvP.allow ch h (.write r) = ∃ q, (kvState h).2 = some q ∧ r = respond (kvState h).1 q := rfl

@[simp, grind =] theorem kvState_read_ok (h) (q : KVReq) :
    kvState (h ++ [.read (.ok q)]) = ((kvState h).1, some q) := by
  simp [kvState, List.foldl_append]
/-- Answering the pending request applies it to the store. -/
def kvWrite : Store × Option KVReq → Store × Option KVReq
  | (st, some q) => (apply st q, none)
  | (st, none) => (st, none)

@[simp, grind =] theorem kvWrite_some (st : Store) (q : KVReq) : kvWrite (st, some q) = (apply st q, none) := rfl

@[simp, grind =] theorem kvState_write_ok (h) (r : KVResp) (u : Unit) :
    kvState (h ++ [.write r (.ok u)]) = kvWrite (kvState h) := by
  simp only [kvState, List.foldl_append, List.foldl_cons, List.foldl_nil]
  generalize List.foldl _ _ h = acc
  obtain ⟨st, p⟩ := acc
  cases p <;> rfl

@[simp, grind =] theorem kvP_onReply_read_ok (ch h) (q : KVReq) : kvP.onReply ch h .read (.ok q) = True := rfl
@[simp, grind =] theorem kvP_onReply_read_error (ch h) (e : IOErr) :
    kvP.onReply ch h .read (.error e) = (e = .eof) := rfl
@[simp, grind =] theorem kvP_onReply_write_ok (ch h) (o : KVResp) (u : Unit) :
    kvP.onReply ch h (.write o) (.ok u) = True := rfl
@[simp, grind =] theorem kvP_onReply_write_error (ch h) (o : KVResp) (e : IOErr) :
    kvP.onReply ch h (.write o) (.error e) = False := rfl

abbrev KVEv := KV × IOEvent KVReq KVResp IOErr

/-- What each key-value client sends. -/
class KVClients where
  requests : KV → List KVReq

/-- A key-value connection delivers its client's requests in order, then the end of input. -/
def kvModel [KVClients] (c : KV) (h : List (IOEvent KVReq KVResp IOErr)) :
    StreamOp KVReq KVResp α → Except IOErr α
  | .read => nextInput (KVClients.requests c) h
  | .write _ => .ok ()

instance [KVClients] : PureModel KV kvP KVEv where
  call t c o := kvModel c (t.traceOf c) o
  call_ok t c o := by
    cases o with
    | read =>
      simp only [kvModel, nextInput]
      split <;> first | trivial | rfl
    | write _ => trivial

/-- Serving `qs` from an empty store: the history it produces, and the store after. -/
def serveAll (qs : List KVReq) : List (IOEvent KVReq KVResp IOErr) × Store :=
  qs.foldl (fun (t, st) q => (t ++ [.read (.ok q), .write (respond st q) (.ok ())], apply st q))
    ([], fun _ => none)

@[simp, grind =] theorem serveAll_nil : serveAll [] = ([], fun _ => none) := rfl

@[simp, grind =] theorem serveAll_concat (qs : List KVReq) (q : KVReq) :
    serveAll (qs ++ [q]) =
      ((serveAll qs).1 ++ [.read (.ok q), .write (respond (serveAll qs).2 q) (.ok ())],
        apply (serveAll qs).2 q) := by
  simp [serveAll, List.foldl_append]

set_option velvet.semantics.termination "partial" in
method kvServe [KVClients] (c : KV) returns (r : Unit) in IOProg KVEv IOErr
  given (h₀ : Trace KVEv)
  requires (h : Trace KVEv) => h = h₀ ∧ kvState (h.traceOf c) = (fun _ => none, none)
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
        store = (serveAll served.reveal).2 ∧ kvState (h.traceOf c) = (store, none))
  do
    let q ← read c
    write c (respond store q)
    store := apply store q
    served *:= served ++ [q]

prove_correct kvServe by
  velvet_vcgen [kvServe] with finish

end Velvet.Examples.IO.Servers.KV
