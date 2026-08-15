import Velvet2.Syntax

/-
# Error message examples

These commands intentionally fail and use `#guard_msgs` to pin the exact error message. If an
error message regresses (text, location, or when it fires), this file fails to build.
-/

/- In total correctness, `while'` must carry a `decreasing` clause. -/
/-- error: `while'` requires a `decreasing` clause in total correctness; add `decreasing <measure>` or use partial correctness -/
#guard_msgs in
method badWhilePrime (n : Nat) returns (res : Nat)
  requires True
  ensures res = 0
do
  let mut i := 0
  while' i < n
    invariant True
  do
    i := i + 1
  return 0
