module

public import Velvet
public meta import Velvet

open Std.WP

/-!
# Loop control flow

`break`, `continue` and `return` inside `while` and `for` loops.

Without `done_with`, every exit goes straight to the code after the loop, with what is known at
the exit: after a `break` the code after the loop is verified from the state at the `break`, after
the condition turns false it is verified from the invariants and the negated condition, and a
`return` is checked against `ensures` where it happens. With `done_with`, a `break` or the normal
exit establishes the invariants and the `done_with` condition, the code after the loop starts from
those alone, and a `return` still goes straight to `ensures`. `continue` re-establishes the
invariants, like the end of the body.

`LoopControlVCs.lean` pins the verification conditions of these methods, and
`LoopVCGenUpstreamIssue.lean` shows how Lean's own `vcgen` handles the same loops.
-/

namespace Velvet.Examples.LoopControl

set_option experimental.vcgen true
set_option experimental.intrinsic true

/-! ## `while` with `break` -/

method breakAtFive (n : Nat) returns (res : Nat)
  ensures res_le: res ≤ n
do
  let mut i := 0
  while i < n
    invariant bound: i ≤ n
    decreasing n - i
  do
    if i = 5 then break
    i := i + 1
  return i

prove_correct breakAtFive by
  velvet_vcgen [breakAtFive] with finish

/- Each exit verifies the code after the loop separately, with its own facts. -/
method twoBreaks (n : Nat) returns (res : Nat)
  ensures res_le: res ≤ n + 1
do
  let mut i := 0
  while i < n
    invariant bound: i ≤ n
    decreasing n - i
  do
    if i = 5 then break
    if i = 7 then break
    i := i + 1
  let j := i + 1
  return j

prove_correct twoBreaks by
  velvet_vcgen [twoBreaks] with finish

/- After the `break`, `x = 10` and `a ≥ 10`; after the condition turns false, `t = 0`, so `x = a`
and `a < 10`. -/
set_option velvet.semantics.termination "partial" in
method countToTen (a : Nat) returns (res : Nat)
  ensures res_min: res = min a 10
do
  let mut x := 0
  let mut t := a
  while loop_cond: t > 0
    invariant progress: x + t = a
    invariant below: x < 10
  do
    x := x + 1
    t := t - 1
    if x = 10 then
      break
  return x

prove_correct countToTen by
  velvet_vcgen [countToTen] with finish

/- With `done_with`, the code after the loop starts from the invariants and `fin` alone: what held
at the `break` is gone, so `i + 1 ≤ n` cannot be proved. Without `done_with` it holds on every
path. -/
method breakDoneCut (n : Nat) returns (res : Nat)
  ensures res_le: res ≤ n
do
  let mut i := 0
  while i < n
    invariant bound: i ≤ n
    decreasing n - i
    done_with fin: i ≤ n
  do
    if i = 5 then break
    i := i + 1
  return i + 1

/--
error: unsolved goals
case res_le
n✝ i : Nat
bound fin : i ≤ n✝
⊢ i + 1 ≤ n✝
-/
#guard_msgs in
prove_correct breakDoneCut by
  velvet_vcgen [breakDoneCut] with try finish

/-! ## `while` with `continue` -/

set_option velvet.semantics.termination "partial" in
method skipEvens (a : Nat) returns (res : Nat)
  ensures res_eq: res = a
do
  let mut x := 0
  let mut t := a
  let mut cnt := 0
  while loop_cond: t > 0
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

/-! ## `while` with `return` -/

/- The `return` is checked against `ensures` where it happens, so `xs[i]! = 0` is known there. -/
method findZero (xs : Array Nat) returns (res : Nat)
  signals notFound: (e : String) => e = "no zero"
  ensures found: res < xs.size ∧ xs[res]! = 0
do
  let mut i := 0
  while i < xs.size
    invariant bound: i ≤ xs.size
    decreasing xs.size - i
  do
    if xs[i]! = 0 then return i
    i := i + 1
  throw "no zero"

prove_correct findZero by
  velvet_vcgen [findZero] with finish

/- With `done_with`, the `break` and the normal exit establish `fin`; the `return` still goes to
`ensures`. -/
method findZeroDone (xs : Array Nat) returns (res : Nat)
  signals notFound: (e : String) => e = "no zero"
  ensures found: res < xs.size ∧ xs[res]! = 0
do
  let mut i := 0
  while i < xs.size
    invariant bound: i ≤ xs.size
    decreasing xs.size - i
    done_with fin: i ≤ xs.size
  do
    if xs[i]! = 0 then return i
    if xs[i]! = 7 then break
    i := i + 1
  throw "no zero"

prove_correct findZeroDone by
  velvet_vcgen [findZeroDone] with finish

set_option velvet.semantics.termination "partial" in
method findZeroPartial (xs : Array Nat) returns (res : Nat)
  signals notFound: (e : String) => e = "no zero"
  ensures found: res < xs.size ∧ xs[res]! = 0
do
  let mut i := 0
  while i < xs.size
    invariant bound: i ≤ xs.size
  do
    if xs[i]! = 0 then return i
    if xs[i]! = 7 then break
    i := i + 1
  throw "no zero"

prove_correct findZeroPartial by
  velvet_vcgen [findZeroPartial] with finish

set_option velvet.semantics.termination "partial" in
method searchArray (a : Array Nat) (target : Nat) returns (found : Bool)
  ensures found_iff: found = true ↔ ∃ j, j < a.size ∧ a[j]! = target
do
  let mut i := 0
  while i < a.size
    invariant i_le: i ≤ a.size
    invariant not_before: ∀ j, j < i → a[j]! ≠ target
    done_with all_checked: i = a.size
  do
    if a[i]! = target then
      return true
    i := i + 1
  return false

prove_correct searchArray by
  velvet_vcgen [searchArray] with finish

/- A `return` inside a nested `do` block leaves only that block: `v` is its value. -/
method nestedDoReturn (xs : Array Nat) returns (res : Nat)
  ensures res_cases: res = xs.size ∨ (res < xs.size ∧ xs[res]! = 0)
do
  let mut i := 0
  while i < xs.size
    invariant bound: i ≤ xs.size
    decreasing xs.size - i
  do
    let v ← (do
      if xs[i]! = 0 then return 100
      return xs[i]! + 200)
    if v = 100 then return i
    i := i + 1
  return xs.size

prove_correct nestedDoReturn by
  velvet_vcgen [nestedDoReturn] with finish

/-! ## Several loops -/

method seqLoops (n : Nat) returns (res : Nat)
  ensures res_le: res ≤ 2 * n
do
  let mut i := 0
  let mut j := 0
  while i < n
    invariant b1: i ≤ n
    decreasing n - i
  do
    if i = 5 then break
    i := i + 1
  let mut acc := 0
  while j < n
    invariant b2: j ≤ n ∧ acc ≤ j
    decreasing n - j
  do
    if j = 3 then break
    acc := acc + 1
    j := j + 1
  return i + acc

prove_correct seqLoops by
  velvet_vcgen [seqLoops] with finish

/- A `return` from the inner loop leaves both loops and is checked against `ensures`. -/
method nestedFind (xs : Array (Array Nat)) returns (res : Nat × Nat)
  signals notFound: (e : String) => e = "none"
  ensures found: res.1 < xs.size ∧ res.2 < xs[res.1]!.size ∧ xs[res.1]![res.2]! = 0
do
  let mut i := 0
  while i < xs.size
    invariant bi: i ≤ xs.size
    decreasing xs.size - i
  do
    let mut j := 0
    while j < xs[i]!.size
      invariant bj: j ≤ xs[i]!.size
      decreasing xs[i]!.size - j
    do
      if xs[i]![j]! = 0 then return (i, j)
      if xs[i]![j]! = 1 then break
      j := j + 1
    i := i + 1
  throw "none"

prove_correct nestedFind by
  velvet_vcgen [nestedFind] with finish

/-! ## `for` -/

/- The loop state starts with an `Option`, which is not a return slot. -/
method findFirstPositive (xs : List Int) returns (res : Option Int)
  ensures res_pos: ∀ v, res = some v → v > 0 ∧ v ∈ xs
do
  let mut found : Option Int := none
  for x in xs
    invariant none_yet: found = none
  do
    if x > 0 then
      found := some x
      break
  return found

prove_correct findFirstPositive by
  velvet_vcgen [findFirstPositive] with finish

method sumPositives (xs : List Int) returns (sum : Int)
  ensures sum_nonneg: sum ≥ 0
do
  let mut s : Int := 0
  for x in xs
    invariant s_nonneg: s ≥ 0
  do
    if x ≤ 0 then
      continue
    s := s + x
  return s

prove_correct sumPositives by
  velvet_vcgen [sumPositives] with finish

method forReturn (xs : List Nat) returns (res : Nat)
  ensures res_cases: res = 0 ∨ res > 5
do
  let mut seen := 0
  for x in xs
    invariant seen_le: seen ≤ xs.length
  do
    if x > 5 then return x
    if seen < xs.length then seen := seen + 1
  return 0

prove_correct forReturn by
  velvet_vcgen [forReturn] with finish

method containsZero (xs : List Nat) returns (res : Bool)
  ensures found_iff: res = true ↔ 0 ∈ xs
do
  for x in xs
    invariant none_yet: ∀ y ∈ __pref, y ≠ 0
    done_with all_checked: ∀ y ∈ __pref, y ≠ 0
  do
    if x = 0 then
      return true
  return false

prove_correct containsZero by
  velvet_vcgen [containsZero] with finish

method forDoneReturn (n : Nat) returns (res : Nat)
  ensures res_le: res ≤ n
do
  let mut s := 0
  for i in List.range n
    invariant s_le: s ≤ __pref.length
    done_with fin: s ≤ n
  do
    if i * i > n then return i
    s := s + 1
  return s

prove_correct forDoneReturn by
  velvet_vcgen [forDoneReturn] with try finish
  all_goals grind [List.mem_range]

/- Lean's own `for`, without Velvet clauses: a `break` or `return` keeps what is known at it. -/
method forPlainReturn (xs : List Nat) returns (res : Nat)
  ensures res_cases: res = 0 ∨ res > 5
do
  for x in xs do
    if x > 5 then return x
  return 0

prove_correct forPlainReturn by
  velvet_vcgen [forPlainReturn] with finish

method forPlainBreak (xs : List Nat) returns (res : Nat)
  ensures res_cases: res = 0 ∨ res > 5
do
  let mut r := 0
  for x in xs do
    if x > 5 then
      r := x
      break
  if r > 5 then return r
  return 0

prove_correct forPlainBreak by
  velvet_vcgen [forPlainBreak] with finish

end Velvet.Examples.LoopControl
