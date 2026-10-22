import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg

namespace Velvet.Examples.IO.Generic

abbrev Solo := Socket × IOEvent Request Response IOErr

instance : Model reqResp Socket Solo where
  read _ _ := .error .eof
  read_ok _ _ := Or.inl rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

method reply (s : Socket) returns (r : Unit) in IOProg Solo IOErr
  requires (h : Trace Solo) => pending (h.traceOf s) = none
  signals (e : IOErr) (h : Trace Solo) => pending (h.traceOf s) = none
  signals False
  ensures (h : Trace Solo) => pending (h.traceOf s) = none
do
  let q ← read s
  write s (Response.mk q.id)

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

method replyAndLog (s : Socket) returns (r : Unit) in IOProg Both IOErr
  requires (h : Trace Both) => pending (h.traceOf s) = none
  signals (e : IOErr) (h : Trace Both) => e = .eof → pending (h.traceOf s) = none
  signals False
  ensures (h : Trace Both) => pending (h.traceOf s) = none
do
  let q ← read s
  write s (Response.mk q.id)
  write Stdout.mk "replied"

prove_correct replyAndLog by
  velvet_vcgen [replyAndLog] with finish

end Velvet.Examples.IO.Generic
