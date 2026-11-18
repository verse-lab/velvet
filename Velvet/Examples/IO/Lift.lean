import Velvet.Examples.IO.Generic

open Std.WP Lean.Order IOProg
open Velvet.Examples.IO Velvet.Examples.IO.Generic

/-! IO over a base monad: a handler that also counts the requests it serves, in a `StateT Nat`
underneath the IO. Its specs take the counter as well as the trace. -/

namespace Velvet.Examples.IO.Lift

method countedReply [Clients] (s : Socket) returns (q : Request) in IOProgT SockEvent IOErr (StateT Nat Option)
  given (h₀ : Trace SockEvent) (n₀ : Nat)
  requires (h : Trace SockEvent) (n : Nat) => h = h₀ ∧ n = n₀
  signals (e : IOErr) (h : Trace SockEvent) (n : Nat) => True
  signals True
  ensures (h : Trace SockEvent) (n : Nat) =>
    n = n₀ + 1 ∧ h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.ok ()))]
do
  let q ← read s
  modify (· + 1)
  write s (Response.mk q.id)
  return q

prove_correct countedReply by
  velvet_vcgen [countedReply] with finish

section Run

local instance : Clients where
  stdin := []
  stdin_ok := by simp
  logCapacity := 0
  requests _ := [⟨7⟩, ⟨8⟩]
  commands _ := []

def runCounted (n : Nat) : String :=
  match ((countedReply ⟨1⟩).interp (m := IOModelT SockEvent IOErr (StateT Nat Option))).run.run ⟨[]⟩ |>.run n with
  | some ((.ok q, h), n') => s!"request {q.id}, {h.events.length} events, counter {n'}"
  | some ((.error _, _), _) => "error"
  | none => "diverged"

/-- info: "request 7, 2 events, counter 42" -/
#guard_msgs in
#eval runCounted 41

end Run

end Velvet.Examples.IO.Lift
