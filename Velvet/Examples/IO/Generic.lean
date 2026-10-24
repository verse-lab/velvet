import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg

/-! Event types built from products and sums: a channel kind on its own, and two side by side. The
specs state the whole trace, so nothing else may happen. -/

namespace Velvet.Examples.IO.Generic

abbrev Solo := Socket × IOEvent Request Response IOErr

instance [Clients] : Model Socket reqResp Solo where
  call t s o := socketModel s (t.traceOf s) o
  call_ok _ s o := socketModel_ok s _ o

@[simp, grind =] theorem inj_solo (s : Socket) (e) : (Provide.inj s e : Solo) = (s, e) := rfl

method reply [Clients] (s : Socket) returns (q : Request) in IOProg Solo IOErr
  given (h₀ : Trace Solo)
  requires (h : Trace Solo) => h = h₀
  signals (e : IOErr) (h : Trace Solo) =>
    (e = .eof ∨ e = .reset) ∧
      (h.events = h₀.events ++ [(s, .read (.error e))] ∨
        ∃ q : Request, h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.error e))])
  signals False
  ensures (h : Trace Solo) => h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.ok ()))]
do
  let q ← read s
  write s (Response.mk q.id)
  return q

prove_correct reply by
  velvet_vcgen [reply] with finish

abbrev Both := (Stdout × IOEvent String String IOErr) ⊕ Solo

instance : Model Stdout stdoutP Both where
  call _ _ o := stdoutModel o
  call_ok _ ch o := stdoutModel_ok ch _ o

instance [Clients] : Model Socket reqResp Both where
  call t s o := socketModel s (t.traceOf s) o
  call_ok _ s o := socketModel_ok s _ o

@[simp, grind =] theorem inj_both_sock (s : Socket) (e) : (Provide.inj s e : Both) = .inr (s, e) := rfl
@[simp, grind =] theorem inj_both_stdout (ch : Stdout) (e) : (Provide.inj ch e : Both) = .inl (ch, e) := rfl

method replyAndLog [Clients] (s : Socket) returns (q : Request) in IOProg Both IOErr
  given (h₀ : Trace Both)
  requires (h : Trace Both) => h = h₀
  signals (e : IOErr) (h : Trace Both) =>
    (e = .eof ∨ e = .reset) ∧
      (h.events = h₀.events ++ [.inr (s, .read (.error e))] ∨
        (∃ q : Request, h.events = h₀.events ++ [.inr (s, .read (.ok q)), .inr (s, .write ⟨q.id⟩ (.error e))]) ∨
        ∃ q : Request, h.events = h₀.events ++
          [.inr (s, .read (.ok q)), .inr (s, .write ⟨q.id⟩ (.ok ())), .inl (⟨⟩, .write "replied" (.error e))])
  signals False
  ensures (h : Trace Both) =>
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
