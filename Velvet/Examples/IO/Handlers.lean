import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg

/-! Each spec states the whole trace a handler leaves, on success and on every error, so a handler
that also touches another channel does not verify. -/

namespace Velvet.Examples.IO.Handlers

method handleOne [Clients] (s : Socket) returns (q : Request) in Prog
  given (h₀ : Trace Event)
  requires (h : Trace Event) => h = h₀
  signals (e : IOErr) (h : Trace Event) =>
    (e = .eof ∨ e = .reset) ∧
      (h.events = h₀.events ++ [.sock s (.read (.error e))] ∨
        ∃ q : Request, h.events = h₀.events ++ [.sock s (.read (.ok q)), .sock s (.write ⟨q.id⟩ (.error e))])
  signals True
  ensures (h : Trace Event) =>
    h.events = h₀.events ++ [.sock s (.read (.ok q)), .sock s (.write ⟨q.id⟩ (.ok ()))]
do
  let q ← read s
  write s (Response.mk q.id)
  return q

prove_correct handleOne by
  velvet_vcgen [handleOne] with finish

method handleTwo [Clients] (s : Socket) returns (qs : Request × Request) in Prog
  given (h₀ : Trace Event)
  requires (h : Trace Event) => h = h₀
  signals (e : IOErr) (h : Trace Event) =>
    (e = .eof ∨ e = .reset) ∧
      (h.events = h₀.events ++ [.sock s (.read (.error e))] ∨
        (∃ q₁ : Request, h.events = h₀.events ++
          [.sock s (.read (.ok q₁)), .sock s (.write ⟨q₁.id⟩ (.error e))]) ∨
        (∃ q₁ : Request, h.events = h₀.events ++
          [.sock s (.read (.ok q₁)), .sock s (.write ⟨q₁.id⟩ (.ok ())), .sock s (.read (.error e))]) ∨
        ∃ q₁ q₂ : Request, h.events = h₀.events ++
          [.sock s (.read (.ok q₁)), .sock s (.write ⟨q₁.id⟩ (.ok ())),
            .sock s (.read (.ok q₂)), .sock s (.write ⟨q₂.id⟩ (.error e))])
  signals True
  ensures (h : Trace Event) =>
    h.events = h₀.events ++
      [.sock s (.read (.ok qs.1)), .sock s (.write ⟨qs.1.id⟩ (.ok ())),
        .sock s (.read (.ok qs.2)), .sock s (.write ⟨qs.2.id⟩ (.ok ()))]
do
  let q₁ ← read s
  write s (Response.mk q₁.id)
  let q₂ ← read s
  write s (Response.mk q₂.id)
  return (q₁, q₂)

prove_correct handleTwo by
  velvet_vcgen [handleTwo]
  all_goals first | grind | (subst_vars; simp)

method loggedReply [Clients] (s : Socket) returns (q : Request) in Prog
  given (h₀ : Trace Event)
  requires (h : Trace Event) => h = h₀
  signals (e : IOErr) (h : Trace Event) =>
    (h.events = h₀.events ++ [.sock s (.read (.error e))] ∧ (e = .eof ∨ e = .reset)) ∨
      (∃ q : Request, h.events = h₀.events ++ [.sock s (.read (.ok q)), .log (.write "request" (.error e))] ∧
        e = .full) ∨
      (∃ q : Request, h.events = h₀.events ++
        [.sock s (.read (.ok q)), .log (.write "request" (.ok ())), .sock s (.write ⟨q.id⟩ (.error e))] ∧
        (e = .eof ∨ e = .reset))
  signals True
  ensures (h : Trace Event) =>
    h.events = h₀.events ++
      [.sock s (.read (.ok q)), .log (.write "request" (.ok ())), .sock s (.write ⟨q.id⟩ (.ok ()))]
do
  let q ← read s
  write Log.mk "request"
  write s (Response.mk q.id)
  return q

prove_correct loggedReply by
  velvet_vcgen [loggedReply] with finish

method echoLine [Clients] returns (line : String) in Prog
  given (h₀ : Trace Event)
  requires (h : Trace Event) => h = h₀
  signals (e : IOErr) (h : Trace Event) =>
    e = .eof ∧
      (h.events = h₀.events ++ [.stdin (.read (.error e))] ∨
        ∃ line : String, ¬ line.contains '\n' ∧
          h.events = h₀.events ++ [.stdin (.read (.ok line)), .stdout (.write line (.error e))])
  signals True
  ensures (h : Trace Event) =>
    ¬ line.contains '\n' ∧ h.events = h₀.events ++ [.stdin (.read (.ok line)), .stdout (.write line (.ok ()))]
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
method handleCmd [Clients] (a : Auth) (loggedIn? : Bool) returns (cmd : Cmd) in Prog
  given (h₀ : Trace Event)
  requires (h : Trace Event) => h = h₀ ∧ loggedIn? = loggedIn (h.traceOf a)
  signals (e : IOErr) (h : Trace Event) =>
    e = .eof ∧
      (h.events = h₀.events ++ [.auth a (.read (.error e))] ∨
        ∃ cmd : Cmd, h.events = h₀.events ++
          [.auth a (.read (.ok cmd)), .auth a (.write (reply (loggedIn (h₀.traceOf a)) cmd) (.error e))])
  signals True
  ensures (h : Trace Event) =>
    h.events = h₀.events ++
      [.auth a (.read (.ok cmd)), .auth a (.write (reply (loggedIn (h₀.traceOf a)) cmd) (.ok ()))]
do
  let cmd ← read a
  match cmd with
  | .login => write a .ok
  | .fetch => if loggedIn? then write a .ok else write a .denied
  return cmd

prove_correct handleCmd by
  velvet_vcgen [handleCmd] with finish

end Velvet.Examples.IO.Handlers
