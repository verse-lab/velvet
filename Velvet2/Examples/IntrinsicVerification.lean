import Velvet2.Syntax
import Velvet2.Ghost
import Velvet2.Tactics
import Velvet2.VCGen.Frontend

/-!
# Intrinsic Verification Examples

Demonstrating intrinsic verification in Velvet: with `set_option velvet.verifyDuringElab true`,
each `method` declaration is verified automatically during elaboration by `vcgen_ with finish`,
producing the verified `spec.proof` theorem without requiring a separate `prove_correct` block.
-/

namespace Velvet2.Examples.IntrinsicVerification

set_option velvet.verifyDuringElab true
set_option maxHeartbeats 10000000

/-! ## Basic Pure and Arithmetic Methods -/

method absDiff (x : Nat) (y : Nat)
  returns (res : Nat)
  ensures res ≥ 0
  ensures x ≥ y → res = x - y
do
  if x ≥ y then
    return x - y
  else
    return y - x

#check absDiff.spec

method maxOf (x : Nat) (y : Nat)
  returns (res : Nat)
  ensures max_ge_x : res ≥ x
  ensures max_ge_y : res ≥ y
do
  if x ≥ y then
    return x
  else
    return y

#check maxOf.spec

/-! ## Loops with `for'` and `while'` -/

/- Accumulate even contributions over a finite range. Automatically verified during elaboration! -/
method sumDoubleRange (n : Nat)
  returns (result : Nat)
  requires precond: True
  ensures result_even: result % 2 = 0
do
  let mut acc := 0
  for' i in 0...n
    invariant accumulator_even: acc % 2 = 0
    done_with sum_done: acc % 2 = 0
  do
    acc := acc + 2 * i
  return acc

#check sumDoubleRange.spec

/- Array scan with `while'` and inline annotations. -/
method isGreaterInline (n : Int) (a : Array Int)
  returns (result : Bool)
  requires precond: True
  ensures postcond: result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let mut ok := true
  let mut i : Nat := 0
  while' loop_cond: i < a.size
    invariant idx_nonneg: 0 ≤ i
    invariant idx_bounded: i ≤ a.size
    invariant ok_iff_prefix: ok = true ↔ (∀ j : Nat, j < i → a[j]! < n)
    decreasing by_size: a.size - i
    done_with loop_done: a.size ≤ i
  do
    if a[i]! < n then
      ok := ok
    else
      ok := false
    i := i + 1
  return ok

#check isGreaterInline.spec

/-! ## Partial Correctness Loops -/

set_option velvet.semantics.termination "partial" in
method partialCount (n : Nat)
  returns (res : Nat)
  requires True
  ensures res = n
do
  let mut i := 0
  while' i < n
    invariant i_le : i ≤ n
    decreasing remaining : n - i
  do
    i := i + 1
  return i

#check partialCount.spec

set_option velvet.semantics.termination "partial" in
method spin
  returns (res : Nat)
  requires True
  ensures True
do
  let mut i := 0
  while' True
    invariant True
  do
    i := i + 1
  return 0

#check spin.spec

set_option velvet.semantics.termination "partial" in
method partialCountNoMeasure (n : Nat)
  returns (res : Nat)
  requires True
  ensures res = n
do
  let mut i := 0
  while' i < n
    invariant i_le : i ≤ n
  do
    i := i + 1
  return i

#check partialCountNoMeasure.spec

set_option velvet.semantics.termination "partial" in
method partialTick
  returns (res : Nat)
  requires True
  ensures True
do
  let mut i := 0
  while' True
    invariant i_nonneg : i ≥ 0
  do
    i := i + 1
  return i

#check partialTick.spec

/-! ## Examples that Fail Automatic Verification (`#guard_msgs`) -/

/- `isGreaterWithCompoundInvariant`: contains a compound `∧` invariant and array bounds refinement
that `finish` cannot automatically discharge, leaving 1 unsolved VC during elaboration. -/
/--
error: `finish` failed
case inv_ok.1
n✝ : Int
a✝¹ : Array Int
size_gt_0 : 0 < a✝¹.size
a✝ : Bool
b✝ : Nat
sz_invariant : 0 ≤ b✝ ∧ b✝ ≤ a✝¹.size
inv_ok : a✝ = true ↔ ∀ (j : Nat), j < b✝ → a✝¹[j]! < n✝
loop_cond : b✝ < a✝¹.size
if_cond : ¬a✝¹[b✝] < n✝
h✝¹ : False = ¬∀ (j : Nat), j ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
left✝ : a✝ = true
right✝ : ∀ (j : Nat), j + 1 ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] 1 ≤ a✝¹.size
    [prop] b✝ ≤ a✝¹.size
    [prop] (a✝ = true) = ∀ (j : Nat), j + 1 ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
    [prop] b✝ + 1 ≤ a✝¹.size
    [prop] n✝ + -1 * a✝¹[b✝] ≤ 0
    [prop] False = ¬∀ (j : Nat), j ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
    [prop] a✝ = true
    [prop] ∀ (j : Nat), j + 1 ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
  [eqc] True propositions
    [prop] False = ¬∀ (j : Nat), j ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
    [prop] (a✝ = true) = ∀ (j : Nat), j + 1 ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
    [prop] a✝ = true
    [prop] n✝ + -1 * a✝¹[b✝] ≤ 0
    [prop] b✝ ≤ a✝¹.size
    [prop] 1 ≤ a✝¹.size
    [prop] b✝ + 1 ≤ a✝¹.size
    [prop] b✝ < a✝¹.size
    [prop] ∀ (j : Nat), j ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
    [prop] ∀ (j : Nat), j + 1 ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
  [eqc] False propositions
    [prop] ¬∀ (j : Nat), j ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
  [eqc] Equivalence classes
    [eqc] {a✝, true}
  [cases] Case analyses
    [cases] [1/2]: (a✝ = true) = ∀ (j : Nat), j + 1 ≤ b✝ → -1 * n✝ + a✝¹[j]! + 1 ≤ 0
      [cases] source: Initial goal
  [ematch] E-matching patterns
    [thm] Array.eq_empty_of_size_eq_zero: [@Array.size #2 #1]
    [thm] local_0: [@LE.le `[Nat] `[instLENat] #1 `[b✝]]
    [thm] local_0: [@LE.le `[Int] `[Int.instLEInt] (@HAdd.hAdd `[Int] `[Int] `[Int] `[instHAdd] (@HAdd.hAdd `[Int] `[Int] `[Int] `[instHAdd] `[-1 *
             n✝] (@getElem! `[Array
              Int] `[Nat] `[Int] `[fun xs i =>
              i < xs.size] `[Array.instGetElem?NatLtSize] `[Int.instInhabited] `[a✝¹] #1)) `[1]) `[0]]
    [thm] local_0: [@getElem! `[Array
           Int] `[Nat] `[Int] `[fun xs i => i < xs.size] `[Array.instGetElem?NatLtSize] `[Int.instInhabited] `[a✝¹] #1]
    [thm] local_1: [@LE.le `[Nat] `[instLENat] (@HAdd.hAdd `[Nat] `[Nat] `[Nat] `[instHAdd] #1 `[1]) `[b✝]]
    [thm] local_1: [@LE.le `[Int] `[Int.instLEInt] (@HAdd.hAdd `[Int] `[Int] `[Int] `[instHAdd] (@HAdd.hAdd `[Int] `[Int] `[Int] `[instHAdd] `[-1 *
             n✝] (@getElem! `[Array
              Int] `[Nat] `[Int] `[fun xs i =>
              i < xs.size] `[Array.instGetElem?NatLtSize] `[Int.instInhabited] `[a✝¹] #1)) `[1]) `[0]]
    [thm] local_1: [@getElem! `[Array
           Int] `[Nat] `[Int] `[fun xs i => i < xs.size] `[Array.instGetElem?NatLtSize] `[Int.instInhabited] `[a✝¹] #1]
    [thm] local_1: [@LE.le `[Nat] `[instLENat] (#1 + 1) `[b✝]]
  [cutsat] Assignment satisfying linear constraints
    [assign] n✝ := 0
    [assign] b✝ := 0
    [assign] a✝¹.size := 1
    [assign] a✝¹[b✝] := 0
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] local_0 ↦ 7
    [thm] getElem!_neg ↦ 4
    [thm] getElem!_pos ↦ 4
-/
#guard_msgs (error) in
method isGreaterWithCompoundInvariant (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let mut ok := true
  let mut i : Nat := 0
  while' loop_cond: i < a.size
    invariant sz_invariant: 0 ≤ i ∧ i ≤ a.size
    invariant inv_ok: ok = true ↔ (∀ j : Nat, j < i → a[j]! < n)
    decreasing by_size: a.size - i
    done_with h_done : a.size ≤ i
  do
    if a[i]'(loop_cond) < n then
      ok := ok
    else
      ok := false
    i := i + 1
  return ok

set_option velvet.semantics.termination "partial" in
method partialTickWithGhost
  returns (res : Nat)
  requires True
  ensures True
do
  let mut i := 0
  let ghost ctr := 0
  while' True
    invariant i_nonneg : i ≥ 0
    invariant ghost_ctr : ctr.reveal = i
  do
    i := i + 1;
    *ctr := ctr + 1
  return i

end Velvet2.Examples.IntrinsicVerification
