import Velvet2.Syntax
import Velvet2.Ghost
import Velvet2.VCGen.Frontend


set_option maxHeartbeats 10000000

method isGreaterWithInvariants (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let mut ok := true
  let mut i : Nat := 0
  while' loop_cond: i < a.size
    invariant sz_invariant: 0 ≤ i ∧ i ≤ a.size
    -- I'd like to be able to access loop_cond here too..
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

    
prove_correct isGreaterWithInvariants by
  vcgen_ [isGreaterWithInvariants] with try finish
  case inv_ok =>
    rename_i n a ok i
    refine ⟨fun h => False.elim h, fun h => ?_⟩
    have this := h i (by omega)
    rw [getElem!_pos a i (by omega)] at this
    exact if_cond this

/- The same loop written with Lean's ordinary `while` syntax. -/
def isGreaterNativeWhile (n : Int) (a : Array Int) : Option Bool := do
  let mut ok := true
  let mut i := 0
  while i < a.size do
    if a[i]! < n then
      ok := ok
    else
      ok := false
    i := i + 1
  return ok

/- A native `vcgen` proof with the loop invariant and variant supplied manually. -/
theorem isGreaterNativeWhile_correct (n : Int) (a : Array Int) :
    Std.Internal.Do.Triple (isGreaterNativeWhile n a)
      (Named.mk `precond Option.none True)
      (Named.mk `postcond Option.none (fun result => result = true ↔ ∀ i, i < a.size → a[i]! < n))
      True := by
  vcgen_ [isGreaterNativeWhile] invariants
  · fun
    | .inl b =>
        Named.mk `idx_nonneg Option.none (0 ≤ b.snd) ∧
        Named.mk `idx_bounded Option.none (b.snd ≤ a.size) ∧
        Named.mk `ok_iff_prefix Option.none
          (b.fst = true ↔ ∀ j, j < b.snd → a[j]! < n)
    | .inr b =>
        (Named.mk `idx_nonneg Option.none (0 ≤ b.snd) ∧
         Named.mk `idx_bounded Option.none (b.snd ≤ a.size) ∧
         Named.mk `ok_iff_prefix Option.none
           (b.fst = true ↔ ∀ j, j < b.snd → a[j]! < n)) ∧
        Named.mk `loop_done Option.none (a.size ≤ b.snd)
  · Std.Internal.Do.RepeatVariant.ofMeasure (Pred := Prop)
      (fun b => a.size - b.snd)
  with finish

/- The same loop using Velvet's inline loop annotations. -/
method isGreaterInlineAnnotations (n : Int) (a : Array Int)
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

prove_correct isGreaterInlineAnnotations by
  vcgen_ [isGreaterInlineAnnotations] with finish

  
method scanRangeVCGen (n : Nat)
  returns (result : Unit)
  requires precond: True
  ensures postcond: True
do
  for' i in 0...n
    invariant cursor_reflexive: i = i
    done_with scan_done: True
  do
    pure ()
  return ()

prove_correct scanRangeVCGen by
  vcgen_ [scanRangeVCGen] with finish




/- Accumulate even contributions over a finite range.
Demonstrates pure state invariant: invariant holds at entry, step, and exit without `done_with`. -/
method sumDoubleRange (n : Nat)
  returns (result : Nat)
  requires precond: True
  ensures result_even: result % 2 = 0
do
  let mut acc := 0
  for' i in 0...n
    invariant accumulator_even: acc % 2 = 0
  do
    acc := acc + 2 * i
  return acc

prove_correct sumDoubleRange by
  vcgen_ [sumDoubleRange] with finish

/- Track the most recently visited value while preserving a simple bound. -/
method boundedRangeValues (n : Nat)
  returns (result : Nat)
  requires precond: True
  ensures result_nonnegative: result ≥ 0
do
  let mut last := 0
  for' i in 0...n
    invariant last_nonnegative: last ≥ 0
  do
    last := i
  return last

prove_correct boundedRangeValues by
  vcgen_ [boundedRangeValues] with finish

/- Loop over two mutable variables simultaneously.
Demonstrates cursor-dependent invariant with explicit `done_with` exit clause. -/
method twoVar (n : Nat) returns (r : Nat)
  ensures r_eq: r = n
do
  let mut x := 0
  let mut y := 0
  for' i in List.range n
    invariant xy: x = i ∧ y = i
    done_with d: x = n ∧ y = n
  do
    x := x + 1
    y := y + 1
  return x

theorem twoVar_correct : twoVar.spec_triple := by
  unfold twoVar.spec_triple
  vcgen_ [twoVar] with try finish
  case xy =>
    rename_i cur rest h
    rw [Std.Internal.ForIn.toList_list] at h
    have := list_range_head h
    omega
  case xy =>
    rename_i pref cur next rest h b
    rw [Std.Internal.ForIn.toList_list] at h
    have := list_range_next h
    omega
  case d =>
    rename_i pref cur h b
    rw [Std.Internal.ForIn.toList_list] at h
    have := list_range_last h
    omega

/-! ### Non-Membership Loop (`forIn`) -/

/- Summing a list of natural numbers with standard `forIn` (no membership proof bound, pure state invariant). -/
method sumList (xs : List Nat)
  returns (sum : Nat)
  requires precond: True
  ensures sum_nonneg: sum ≥ 0
do
  let mut s := 0
  for' x in xs
    invariant s_nonneg: s ≥ 0
  do
    s := s + x
  return s

prove_correct sumList by
  vcgen_ [sumList] with finish

/-! ### Membership Loop (`forIn'`) -/

/- Iterating with membership proof `h : x ∈ xs` in scope (elaborates to `forIn'`). -/
method memberElementBound (xs : List Nat) (bound : Nat)
  returns (sum : Nat)
  requires all_le: ∀ x ∈ xs, x ≤ bound
  ensures sum_nonneg: sum ≥ 0
do
  let mut s := 0
  for' h : x in xs
    invariant nonneg: s ≥ 0
  do
    assert h_in: x ∈ xs
    s := s + x
  return s

prove_correct memberElementBound by
  vcgen_ [memberElementBound] with finish


/- Method-call composition: delegates to `isGreaterWithInvariants`. -/
method isGreaterWithInvariants' (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let res <- isGreaterWithInvariants n a
  return res

prove_correct isGreaterWithInvariants' by
  vcgen_ [isGreaterWithInvariants'] with finish

/- Partial correctness: a terminating `while'` loop still carries a `decreasing` measure and
is fully provable. -/
set_option velvet.semantics.termination "partial" in
method partialCount (n : Nat) returns (res : Nat)
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

prove_correct partialCount by
  vcgen_ [partialCount] with finish

/- A genuinely non-terminating `while'` loop omits `decreasing`; it is only valid under partial
correctness, and its spec is discharged by our least-fixed-point loop rule. -/
set_option velvet.semantics.termination "partial" in
method spin returns (res : Nat)
  requires True
  ensures True do
  let mut i := 0
  while' True
    invariant True
  do
    i := i + 1
  return 0

prove_correct spin by
  vcgen_ [spin] with finish

/- A terminating loop that omits `decreasing`: the invariant plus the exit condition still pins
the result, so partial correctness proves the same postcondition without a measure. -/
set_option velvet.semantics.termination "partial" in
method partialCountNoMeasure (n : Nat) returns (res : Nat)
  requires True
  ensures res = n
do
  let mut i := 0
  while' i < n
    invariant i_le : i ≤ n
  do
    i := i + 1
  return i

prove_correct partialCountNoMeasure by
  vcgen_ [partialCountNoMeasure] with finish

/- A non-terminating loop still maintains a meaningful invariant. -/
set_option velvet.semantics.termination "partial" in
method partialTick returns (res : Nat)
  requires True
  ensures True do
  let mut i := 0
  while' True
    invariant i_nonneg : i ≥ 0
  do
    i := i + 1
  return i

prove_correct partialTick by
  vcgen_ [partialTick] with finish

set_option velvet.semantics.termination "partial" in
method partialTick' returns (res : Nat)
  requires True
  ensures True do
  let mut i := 0
  let ghost ctr := 0
  while' True
    invariant i_nonneg : i ≥ 0
    invariant ghost_ctr : ctr.reveal = i
  do
    i := i + 1;
    *ctr := ctr + 1
  return i

prove_correct partialTick' by
  vcgen_ [partialTick'] with finish
  
