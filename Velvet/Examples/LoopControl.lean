module

public import Velvet
public meta import Velvet

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
  velvet_vcgen [countToTen] with finish

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
  velvet_vcgen [skipEvens] with finish

/- `while'` loop with early return. -/
set_option velvet.semantics.termination "partial" in
method searchArray (a : Array Nat) (target : Nat) returns (found : Bool)
  ensures True
do
  let mut i := 0
  while' i < a.size
    invariant i_le: i ≤ a.size
    done_with done: True
  do
    if a[i]! = target then
      return true
    i := i + 1
  return false

prove_correct searchArray by
  velvet_vcgen [searchArray] with finish

/- `for'` loop with `break`. -/
set_option velvet.semantics.termination "partial" in
method findFirstPositive (xs : List Int) returns (res : Option Int)
  ensures True
do
  let mut found : Option Int := none
  for' x in xs
    invariant found_inv: True
    done_with done: True
  do
    if x > 0 then
      found := some x
      break
  return found

prove_correct findFirstPositive by
  velvet_vcgen [findFirstPositive] with finish

/- `for'` loop with `continue`. -/
set_option velvet.semantics.termination "partial" in
method sumPositives (xs : List Int) returns (sum : Int)
  ensures sum_nonneg: sum ≥ 0
do
  let mut s : Int := 0
  for' x in xs
    invariant s_nonneg: s ≥ 0
  do
    if x ≤ 0 then
      continue
    s := s + x
  return s

prove_correct sumPositives by
  velvet_vcgen [sumPositives] with finish

/- `for'` loop with early `return`. -/
set_option velvet.semantics.termination "partial" in
method containsZero (xs : List Nat) returns (res : Bool)
  ensures True
do
  for' x in xs
    invariant True
    done_with done: True
  do
    if x = 0 then
      return true
  return false

prove_correct containsZero by
  velvet_vcgen [containsZero] with finish

