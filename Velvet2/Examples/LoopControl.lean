import Velvet2.Syntax
import Velvet2.VCGen.Frontend

open Std.Internal.Do

set_option velvet.semantics.termination "partial" in
method countToTen (a : Nat)
  returns (res : Nat)
  requires a_pos: a > 0
  ensures res_pos: res > 0
do
  let mut x := 0
  let mut t := a
  while' loop_cond: t > 0
    invariant progress: x + t = a
    done_with done: x = 10 ∨ t = 0
  do
    x := x + 1
    t := t - 1
    if x = 10 then
      break
  return x

prove_correct countToTen by
  vcgen_ [countToTen] with finish

set_option velvet.semantics.termination "partial" in
method skipEvens (a : Nat)
  returns (res : Nat)
  requires a_pos: a > 0
  ensures res_pos: res ≥ 0
do
  let mut x := 0
  let mut t := a
  let mut cnt := 0
  while' loop_cond: t > 0
    invariant progress: x + t = a
    done_with done: t = 0
  do
    cnt := cnt + 1
    if cnt % 2 = 0 then
      continue
    x := x + 1
    t := t - 1
  return x

prove_correct skipEvens by
  vcgen_ [skipEvens] with finish
