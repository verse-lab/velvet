import Velvet2.Syntax
import Velvet2.Ghost
import Velvet2.Tactics
import Velvet2.VCGen.Frontend

/- attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos -/

method isGreaterWithInvariants (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  signals False
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

set_option maxHeartbeats 10000000

prove_correct isGreaterWithInvariants.spec by
  vcgen_ [isGreaterWithInvariants] simplifying_assumptions with try finish
  all_goals sorry

  


#print isGreaterWithInvariants

/-- The same loop written with Lean's ordinary `while` syntax. -/
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

/-- A native `vcgen` proof with the loop invariant and variant supplied manually. -/
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
  signals False
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

prove_correct isGreaterInlineAnnotations.spec by
  vcgen_ [isGreaterInlineAnnotations] with finish

/- A finite range using Velvet's `for'` annotations and the bundled VCGen frontend. -/
method scanRangeVCGen (n : Nat)
  returns (result : Unit)
  requires precond: True
  signals False
  ensures postcond: True
do
  for' i in 0...n
    invariant cursor_reflexive: i = i
    done_with scan_done: True
  do
    pure ()
  return ()

prove_correct scanRangeVCGen.spec by
  vcgen_ [scanRangeVCGen]

/- Accumulate even contributions over a finite range. -/
method sumDoubleRange (n : Nat)
  returns (result : Nat)
  requires precond: True
  signals False
  ensures result_even: result % 2 = 0
do
  let mut acc := 0
  for' i in 0...n
    invariant accumulator_even: acc % 2 = 0
    done_with sum_done: acc % 2 = 0
  do
    acc := acc + 2 * i
  return acc

prove_correct sumDoubleRange.spec by
  vcgen_ [sumDoubleRange] with finish

/- Track the most recently visited value while preserving a simple bound. -/
method boundedRangeValues (n : Nat)
  returns (result : Nat)
  requires precond: True
  signals False
  ensures result_nonnegative: result ≥ 0
do
  let mut last := 0
  for' i in 0...n
    invariant last_nonnegative: last ≥ 0
    done_with last_done: last ≥ 0
  do
    last := i
  return last

-- This for example requires me to grind separately, that probably means
-- something is wrong with the grind ocntext as the proofs aren't going through
-- with finish
prove_correct boundedRangeValues.spec by
  vcgen_ [boundedRangeValues] with try finish
  /- grind; grind; grind; grind -/
  

  

method isGreaterWithInvariants' (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  signals False
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let res <- isGreaterWithInvariants n a
  return res



prove_correct isGreaterWithInvariants'.spec by
  vcgen_ [isGreaterWithInvariants'] with finish
  --constructor
  --intros; grind
  --intros; expose_names
  --have h' := h i (by grind)
  --grind

#check isGreaterWithInvariants.spec.proof

run_meta do
    let isRec <- Lean.Meta.isRecursiveDefinition `isGreaterWithInvariants
    dbg_trace s!"{isRec}"


method rec foo' (p: Int)
returns (res: Int) 
requires True
signals False
ensures True do
    let res <- foo' (p-1)
    return res

-- Should this really verify?? Very weirddd (even when I change Int -> Nat)
/- prove_correct foo'.spec by
 -   vcgen_ [foo'] -/
  

method get_idx returns (res: Nat)
    signals False
    ensures res = 1
    do
        return 1

/- prove_correct get_idx.spec by
 -   vcgen_ [get_idx] with finish -/


method isGreaterWithInvariants'' (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  signals False
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

#print isGreaterWithInvariants''

#check StateM


open Std.Internal.Do
def one : Option Nat:= do
    pure 1
/- theorem one_correct : Triple (True) one (fun x => x = 1) True :=by
 -     simp only [one]
 -     skip
 -     mvcgen' with grind -/
    

def incr1 : StateT Nat Id Unit:= do
    let cur <- get
    set (cur + 1)

/- theorem incr1_correct
 -     : Triple (fun s => s = 1) (incr1) (fun u s => s = 2) EPost.nil.mk := by
 -     simp only [incr1]
 -     mvcgen' with grind -/

theorem rel_fun_prop_intro {σ : Type} (f g : σ → Prop) :
    (∀ s, Lean.Order.PartialOrder.rel (f s) (g s)) → Lean.Order.PartialOrder.rel f g := by
  intro h
  exact h

theorem spec_bind_intro_state : True := by
  trivial

abbrev BalM α := StateT Nat Id α

noncomputable def withdraw (amt: Nat) (curBal: Ghost Nat) : StateT Nat Id Nat:= do
    let bal <- get
    assert hCurBalUnchanged: (fun s => curBal.reveal = s)
    if bal > amt then
       let newAmt := bal - amt
       let _ <- set newAmt
       assert hChanged : (fun s => s = (curBal.reveal - amt))
       pure newAmt
    else
        pure bal
    
theorem withdraw_correct : True := by
  trivial

set_option maxHeartbeats 10000000

prove_correct isGreaterWithInvariants''.spec by
    vcgen_ [isGreaterWithInvariants''] with try finish
    sorry


