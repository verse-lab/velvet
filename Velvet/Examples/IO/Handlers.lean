import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg

namespace Velvet.Examples.IO.Handlers

method handleOne (s : Socket) returns (q : Request) in Prog
  given (h₀ : Trace Event)
  requires (h : Trace Event) => h = h₀
  signals (e : IOErr) (h : Trace Event) => e = .eof ∨ e = .reset
  signals False
  ensures (h : Trace Event) => h.traceOf s = h₀.traceOf s ++ [.read (.ok q), .write ⟨q.id⟩ .ok]
do
  let q ← read s
  write s (Response.mk q.id)
  return q

prove_correct handleOne by
  velvet_vcgen [handleOne] with finish

method handleTwo (s : Socket) returns (qs : Request × Request) in Prog
  given (h₀ : Trace Event)
  requires (h : Trace Event) => h = h₀
  signals (e : IOErr) (h : Trace Event) => e = .eof ∨ e = .reset
  signals False
  ensures (h : Trace Event) => h.traceOf s = h₀.traceOf s ++
    [.read (.ok qs.1), .write ⟨qs.1.id⟩ .ok, .read (.ok qs.2), .write ⟨qs.2.id⟩ .ok]
do
  let q₁ ← read s
  write s (Response.mk q₁.id)
  let q₂ ← read s
  write s (Response.mk q₂.id)
  return (q₁, q₂)

prove_correct handleTwo by
  velvet_vcgen [handleTwo] with finish

method loggedReply (s : Socket) returns (q : Request) in Prog
  given (h₀ : Trace Event)
  requires (h : Trace Event) => h = h₀
  signals (e : IOErr) (h : Trace Event) => e = .eof ∨ e = .reset ∨ e = .full
  signals False
  ensures (h : Trace Event) =>
    h.traceOf s = h₀.traceOf s ++ [.read (.ok q), .write ⟨q.id⟩ .ok] ∧
      h.traceOf Log.mk = h₀.traceOf Log.mk ++ [.write "request" .ok]
do
  let q ← read s
  write Log.mk "request"
  write s (Response.mk q.id)
  return q

prove_correct loggedReply by
  velvet_vcgen [loggedReply] with finish

method echoLine returns (line : String) in Prog
  given (h₀ : Trace Event)
  requires (h : Trace Event) => h = h₀
  signals (e : IOErr) (h : Trace Event) => e = .eof
  signals False
  ensures (h : Trace Event) =>
    h.traceOf Stdin.mk = h₀.traceOf Stdin.mk ++ [.read (.ok line)] ∧
      h.traceOf Stdout.mk = h₀.traceOf Stdout.mk ++ [.write line .ok]
do
  let s ← read Stdin.mk
  write Stdout.mk s
  return s

prove_correct echoLine by
  velvet_vcgen [echoLine] with finish

/-- The reply to `cmd`, given whether the client has logged in. -/
@[simp, grind =] def reply (loggedIn? : Bool) : Cmd → Reply
  | .login => .ok
  | .fetch => if loggedIn? then .ok else .denied

/- The login state is a parameter, not a ghost: the program branches on it, so it must be real. -/
method handleCmd (a : Auth) (loggedIn? : Bool) returns (cmd : Cmd) in Prog
  given (h₀ : Trace Event)
  requires (h : Trace Event) => h = h₀ ∧ loggedIn? = loggedIn (h.traceOf a)
  signals (e : IOErr) (h : Trace Event) => e = .eof
  signals False
  ensures (h : Trace Event) =>
    h.traceOf a = h₀.traceOf a ++ [.read (.ok cmd), .write (reply (loggedIn (h₀.traceOf a)) cmd) .ok]
do
  let cmd ← read a
  match cmd with
  | .login => write a .ok
  | .fetch => if loggedIn? then write a .ok else write a .denied
  return cmd

prove_correct handleCmd by
  velvet_vcgen [handleCmd] with finish

end Velvet.Examples.IO.Handlers
