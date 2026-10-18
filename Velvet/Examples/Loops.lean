module

public import Velvet
public meta import Velvet

open scoped GhostSyntax


method isGreaterWithInvariants (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let mut ok := true
  let mut i : Nat := 0
  while loop_cond: i < a.size
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

#print isGreaterWithInvariants.spec_triple

set_option velvet_vcgen.showVCReport true in
prove_correct isGreaterWithInvariants by
  velvet_vcgen [isGreaterWithInvariants] with try finish
  case inv_ok =>
    rename_i n a
    constructor <;> intro h
    · cases h
    · have this := h i (by omega)
      have hget : a[i]! = a[i] := getElem!_pos a i (by omega)
      rw [hget] at this
      exact False.elim (by grind)

/- Velvet loops also work inside ordinary definitions. -/
def isGreaterWhileDef (n : Int) (a : Array Int) : Option Bool := do
  let mut ok := true
  let mut i := 0
  while i < a.size
    invariant 0 ≤ i ∧ i ≤ a.size
    invariant ok = true ↔ (∀ j : Nat, j < i → a[j]! < n)
    decreasing a.size - i
  do
    if a[i]! < n then
      ok := ok
    else
      ok := false
    i := i + 1
  return ok

/- Verify the ordinary definition using its inline loop annotations. -/
theorem isGreaterWhileDef_correct (n : Int) (a : Array Int) :
    Std.WP.Triple (isGreaterWhileDef n a)
      (Named.mk `precond Option.none True)
      (Named.mk `postcond Option.none (fun result => result = true ↔ ∀ i, i < a.size → a[i]! < n))
      (fun _ => False) := by
  velvet_vcgen [isGreaterWhileDef] with finish

/- The same loop using Velvet's inline loop annotations. -/
method isGreaterInlineAnnotations (n : Int) (a : Array Int)
  returns (result : Bool)
  requires precond: True
  ensures postcond: result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let mut ok := true
  let mut i : Nat := 0
  while loop_cond: i < a.size
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

prove_correct isGreaterInlineAnnotations by
  velvet_vcgen [isGreaterInlineAnnotations] with finish


method scanRangeVCGen (n : Nat)
  returns (result : Unit)
  requires precond: True
  ensures postcond: True
do
  for i in 0...n
    invariant cursor_reflexive: i = i
    done_with scan_done: True
  do
    pure ()
  return ()

prove_correct scanRangeVCGen by
  velvet_vcgen [scanRangeVCGen] with finish

/- Accumulate even contributions over a finite range.
Demonstrates pure state invariant: invariant holds at entry, step, and exit without `done_with`. -/
method sumDoubleRange (n : Nat)
  returns (result : Nat)
  requires precond: True
  ensures result_even: result % 2 = 0
do
  let mut acc := 0
  for i in 0...n
    invariant accumulator_even: acc % 2 = 0
  do
    acc := acc + 2 * i
  return acc

prove_correct sumDoubleRange by
  velvet_vcgen [sumDoubleRange] with finish

/- Track the most recently visited value while preserving a simple bound. -/
method boundedRangeValues (n : Nat)
  returns (result : Nat)
  requires precond: True
  ensures result_nonnegative: result ≥ 0
do
  let mut last := 0
  for i in 0...n
    invariant last_nonnegative: last ≥ 0
  do
    last := i
  return last

prove_correct boundedRangeValues by
  velvet_vcgen [boundedRangeValues] with finish

/- Pure state invariant over outer mutable variables:
Invariants referencing only outer mutable variables (`x`, `y`) do NOT mention the loop variable `i`,
so NO `done_with` is required. -/
set_option velvet.verifyOnDefinition true in
method twoVarPureState (n : Nat) returns (r : Nat)
  ensures r_even: r % 2 = 0
do
  let mut x := 0
  let mut y := 0
  for i in List.range n
    invariant xy_even: (x + y) % 2 = 0
  do
    x := x + 1
    y := y + 1
  return x + y

/- Loop over two mutable variables with loop-variable dependency:
Because the invariant references the iteration-local loop variable `i` (`x = i ∧ y = i`),
an explicit `done_with` clause is required to specify what holds upon exit. -/
set_option velvet.verifyOnDefinition true in
method twoVar (n : Nat) returns (r : Nat)
  ensures r_eq: r = n
do
  let mut x := 0
  let mut y := 0
  for i in List.range n
    invariant xy: x = i ∧ y = i
    done_with d: x = n ∧ y = n
  do
    x := x + 1
    y := y + 1
  return x

/-! ### Non-Membership Loop (`forIn`) -/

/- Summing a list of natural numbers with standard `forIn` (no membership proof bound, pure state invariant). -/
method sumList (xs : List Nat)
  returns (sum : Nat)
  requires precond: True
  ensures sum_nonneg: sum ≥ 0
do
  let mut s := 0
  for x in xs
    invariant s_nonneg: s ≥ 0
  do
    s := s + x
  return s

prove_correct sumList by
  velvet_vcgen [sumList] with finish

/-! ### Membership Loop (`forIn'`) -/

/- Iterating with membership proof `h : x ∈ xs` in scope (elaborates to `forIn'`). -/
set_option velvet.verifyOnDefinition true in
method memberElementBound (xs : List Nat) (bound : Nat)
  returns (sum : Nat)
  requires all_le: ∀ x ∈ xs, x ≤ bound
  ensures sum_nonneg: sum ≥ 0
do
  let mut s := 0
  for h : x in xs
    invariant nonneg: s ≥ 0
  do
    assert h_in: x ∈ xs
    s := s + x
  return s

/- Method-call composition: delegates to `isGreaterWithInvariants`. -/
method isGreaterWithInvariants' (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let res <- isGreaterWithInvariants n a
  return res

prove_correct isGreaterWithInvariants' by
  velvet_vcgen [isGreaterWithInvariants'] with finish

/- Partial correctness: a terminating `while` loop still carries a `decreasing` measure and
is fully provable. -/
set_option velvet.semantics.termination "partial" in
method partialCount (n : Nat) returns (res : Nat)
  requires True
  ensures res = n
do
  let mut i := 0
  while i < n
    invariant i_le : i ≤ n
    decreasing remaining : n - i
  do
    i := i + 1
  return i

prove_correct partialCount by
  velvet_vcgen [partialCount] with finish

/- A genuinely non-terminating `while` loop omits `decreasing`; it is only valid under partial
correctness, and its spec is discharged by our least-fixed-point loop rule. -/
set_option velvet.semantics.termination "partial" in
method spin returns (res : Nat)
  requires True
  ensures True do
  let mut i := 0
  while i ≥ 0
    invariant True
  do
    i := i + 1
  return 0

prove_correct spin by
  velvet_vcgen [spin] with finish

/- A terminating loop that omits `decreasing`: the invariant plus the exit condition still pins
the result, so partial correctness proves the same postcondition without a measure. -/
set_option velvet.semantics.termination "partial" in
method partialCountNoMeasure (n : Nat) returns (res : Nat)
  requires True
  ensures res = n
do
  let mut i := 0
  while i < n
    invariant i_le : i ≤ n
  do
    i := i + 1
  return i

prove_correct partialCountNoMeasure by
  velvet_vcgen [partialCountNoMeasure] with finish

/- A non-terminating loop still maintains a meaningful invariant. -/
set_option velvet.semantics.termination "partial" in
method partialTick returns (res : Nat)
  requires True
  ensures True do
  let mut i := 0
  while i ≥ 0
    invariant i_nonneg : i ≥ 0
  do
    i := i + 1
  return i

prove_correct partialTick by
  velvet_vcgen [partialTick] with finish

set_option velvet.semantics.termination "partial" in
method partialTick' returns (res : Nat)
  requires True
  ensures True do
  let mut i := 0
  let ghost ctr := 0
  while i ≥ 0
    invariant i_nonneg : i ≥ 0
    invariant ghost_ctr : ctr.reveal = i
  do
    i := i + 1
    ctr *:= ctr + 1
  return i

prove_correct partialTick' by
  velvet_vcgen [partialTick'] with finish

/- A `while` loop without Velvet clauses is Lean's own `while`, so ordinary code keeps compiling
in total correctness. -/
def plainWhile (n : Nat) : Id Nat := do
  let mut i := 0
  while i < n do
    i := i + 1
  return i

def plainWhileIO (n : Nat) : IO Nat := do
  let mut i := 0
  while _h : i < n do
    i := i + 2
  return i

#guard (plainWhile 5).run == 5

/- Likewise, a `for` loop without Velvet clauses is Lean's own `for`. -/
def plainFor (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

#guard plainFor [1, 2, 3] == 6

/- Nested loops followed by another loop: every loop gadget elaborates at the monad's assertion
type, so a single `velvet_vcgen` applies all their specs (verse-lab/velvet#9). -/
method nestedThenLoop (n : Nat) returns (res : Nat)
  requires True
  ensures res = 0
do
  let mut x : Nat := 0
  let mut i : Nat := 0
  while i < n
    decreasing n - i
  do
    let mut j : Nat := 0
    while j < n
      decreasing n - j
    do
      x := 1
      j := j + 1
    i := i + 1
  while x > 0
    decreasing x
  do
    x := x - 1
  return x

prove_correct nestedThenLoop by
  velvet_vcgen [nestedThenLoop] with finish

/- Lean's own `for` loops are verified with the invariant `⊤`. -/
method sumPlainFor (xs : List Nat) returns (r : Nat)
  ensures True
do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

prove_correct sumPlainFor by
  velvet_vcgen [sumPlainFor] with finish

method sumRange (xs : Array Nat) returns (r : Nat)
  ensures True
do
  let mut s := 0
  for h : i in [0:xs.size] do
    s := s + xs[i]
  return s

prove_correct sumRange by
  velvet_vcgen [sumRange] with finish
