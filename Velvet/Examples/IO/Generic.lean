import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg

namespace Velvet.Examples.IO.Generic

abbrev Solo := Socket × IOEvent Request Response IOErr

instance : Model reqResp Socket Solo where
  read _ _ := .error .eof
  read_ok _ _ := Or.inl rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

method reply (s : Socket) returns (q : Request) in IOProg Solo IOErr
  given (h₀ : Trace Solo)
  requires (h : Trace Solo) => h = h₀
  signals (e : IOErr) (h : Trace Solo) => e = .eof ∨ e = .reset
  signals False
  ensures (h : Trace Solo) => h.traceOf s = h₀.traceOf s ++ [.read (.ok q), .write ⟨q.id⟩ .ok]
do
  let q ← read s
  write s (Response.mk q.id)
  return q

prove_correct reply by
  velvet_vcgen [reply] with finish

abbrev Both := (Stdout × IOEvent String String IOErr) ⊕ Solo

instance : Model stdoutP Stdout Both where
  read _ _ := .error .eof
  read_ok _ _ := rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

instance : Model reqResp Socket Both where
  read _ _ := .error .eof
  read_ok _ _ := Or.inl rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

method replyAndLog (s : Socket) returns (q : Request) in IOProg Both IOErr
  given (h₀ : Trace Both)
  requires (h : Trace Both) => h = h₀
  signals (e : IOErr) (h : Trace Both) => e = .eof ∨ e = .reset
  signals False
  ensures (h : Trace Both) =>
    h.traceOf s = h₀.traceOf s ++ [.read (.ok q), .write ⟨q.id⟩ .ok] ∧
      h.traceOf Stdout.mk = h₀.traceOf Stdout.mk ++ [.write "replied" .ok]
do
  let q ← read s
  write s (Response.mk q.id)
  write Stdout.mk "replied"
  return q

prove_correct replyAndLog by
  velvet_vcgen [replyAndLog] with finish

end Velvet.Examples.IO.Generic
