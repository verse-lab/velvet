import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg

namespace Velvet.Examples.IO

method handleOne (s : Socket) returns (r : Unit) in Prog
  requires (h : List Event) => pending (trace h s) = none
  signals (e : IOErr) (h : List Event) => (e = .eof ∨ e = .reset) ∧ pending (trace h s) = none
  signals False
  ensures (h : List Event) => pending (trace h s) = none
do
  let q ← read s
  write s (Response.mk q.id)

prove_correct handleOne by
  velvet_vcgen [handleOne] with finish

method handleTwo (s : Socket) returns (r : Unit) in Prog
  requires (h : List Event) => pending (trace h s) = none
  signals (e : IOErr) (h : List Event) => (e = .eof ∨ e = .reset) ∧ pending (trace h s) = none
  signals False
  ensures (h : List Event) => pending (trace h s) = none
do
  let q₁ ← read s
  write s (Response.mk q₁.id)
  let q₂ ← read s
  write s (Response.mk q₂.id)

prove_correct handleTwo by
  velvet_vcgen [handleTwo] with finish

method loggedReply (s : Socket) returns (r : Unit) in Prog
  requires (h : List Event) => pending (trace h s) = none
  signals (e : IOErr) (h : List Event) => e = .full → pending (trace h s) ≠ none
  signals False
  ensures (h : List Event) => pending (trace h s) = none
do
  let q ← read s
  write Log.mk "request"
  write s (Response.mk q.id)

prove_correct loggedReply by
  velvet_vcgen [loggedReply] with finish

method echoLine returns (r : Unit) in Prog
  given (h₀ : List Event)
  requires (h : List Event) => h = h₀
  signals (e : IOErr) (h : List Event) => e = .eof
  signals False
  ensures (h : List Event) =>
    ∀ s, trace h Stdin.mk = trace h₀ Stdin.mk ++ [.read (.ok s)] →
      trace h Stdout.mk = trace h₀ Stdout.mk ++ [.write s .ok]
do
  let s ← read Stdin.mk
  write Stdout.mk s

prove_correct echoLine by
  velvet_vcgen [echoLine]
  case ensures1 =>
    intro s hs
    simp_all
  all_goals simp_all

method handleCmd (a : Auth) (loggedIn? : Bool) returns (r : Unit) in Prog
  requires (h : List Event) => loggedIn? = loggedIn (trace h a)
  signals (e : IOErr) (h : List Event) => e = .eof
  signals False
  ensures (h : List Event) => True
do
  match ← read a with
  | .login => write a .ok
  | .fetch => if loggedIn? then write a .ok else write a .denied

prove_correct handleCmd by
  velvet_vcgen [handleCmd] with finish

end Velvet.Examples.IO
