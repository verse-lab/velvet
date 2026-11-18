import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg

/-! Event types built from products and sums: a channel kind on its own, and two side by side. The
specs state the whole trace, so nothing else may happen. -/

namespace Velvet.Examples.IO.Generic

abbrev SockEvent := Socket × IOEvent Request Response IOErr

instance [Clients] : PureModel Socket reqResp SockEvent where
  call t s o := socketModel s (t.traceOf s) o
  call_ok _ s o := socketModel_ok s _ o

@[simp, grind =] theorem inj_sockEvent (s : Socket) (e) : (Provide.inj s e : SockEvent) = (s, e) := rfl

method reply [Clients] (s : Socket) returns (q : Request) in IOProg SockEvent IOErr
  given (h₀ : Trace SockEvent)
  requires (h : Trace SockEvent) => h = h₀
  signals (e : IOErr) (h : Trace SockEvent) =>
    (e = .eof ∨ e = .reset) ∧
      (h.events = h₀.events ++ [(s, .read (.error e))] ∨
        ∃ q : Request, h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.error e))])
  signals False
  ensures (h : Trace SockEvent) => h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.ok ()))]
do
  let q ← read s
  write s (Response.mk q.id)
  return q

prove_correct reply by
  velvet_vcgen [reply] with finish

abbrev StdoutSockEvent := (Stdout × IOEvent String String IOErr) ⊕ SockEvent

instance : PureModel Stdout stdoutP StdoutSockEvent where
  call _ _ o := stdoutModel o
  call_ok _ ch o := stdoutModel_ok ch _ o

instance [Clients] : PureModel Socket reqResp StdoutSockEvent where
  call t s o := socketModel s (t.traceOf s) o
  call_ok _ s o := socketModel_ok s _ o

@[simp, grind =] theorem inj_stdoutSock_sock (s : Socket) (e) : (Provide.inj s e : StdoutSockEvent) = .inr (s, e) := rfl
@[simp, grind =] theorem inj_stdoutSock_stdout (ch : Stdout) (e) : (Provide.inj ch e : StdoutSockEvent) = .inl (ch, e) := rfl

method replyAndLog [Clients] (s : Socket) returns (q : Request) in IOProg StdoutSockEvent IOErr
  given (h₀ : Trace StdoutSockEvent)
  requires (h : Trace StdoutSockEvent) => h = h₀
  signals (e : IOErr) (h : Trace StdoutSockEvent) =>
    (e = .eof ∨ e = .reset) ∧
      (h.events = h₀.events ++ [.inr (s, .read (.error e))] ∨
        (∃ q : Request, h.events = h₀.events ++ [.inr (s, .read (.ok q)), .inr (s, .write ⟨q.id⟩ (.error e))]) ∨
        ∃ q : Request, h.events = h₀.events ++
          [.inr (s, .read (.ok q)), .inr (s, .write ⟨q.id⟩ (.ok ())), .inl (⟨⟩, .write "replied" (.error e))])
  signals False
  ensures (h : Trace StdoutSockEvent) =>
    h.events = h₀.events ++
      [.inr (s, .read (.ok q)), .inr (s, .write ⟨q.id⟩ (.ok ())), .inl (⟨⟩, .write "replied" (.ok ()))]
do
  let q ← read s
  write s (Response.mk q.id)
  write Stdout.mk "replied"
  return q

prove_correct replyAndLog by
  velvet_vcgen [replyAndLog]
  all_goals first | grind | (subst_vars; simp)

end Velvet.Examples.IO.Generic
