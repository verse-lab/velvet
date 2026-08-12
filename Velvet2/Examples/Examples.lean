import Velvet2.Syntax
import Velvet2.Ghost
import Velvet2.Tactics
import Velvet2.VCGen.Frontend

/- attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos -/

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

set_option maxHeartbeats 10000000

/- set_option trace.Elab.Tactic.Do.vcgen true -/
prove_correct isGreaterWithInvariants by
  /- vcgen'' [isGreaterWithInvariants] invariants
   - · fun
   -   | .inl b => 0 ≤ b.snd ∧ b.snd ≤ a.size ∧
   -       (b.fst = true ↔ ∀ j, j < b.snd → a[j]! < n)
   -   | .inr b => (0 ≤ b.snd ∧ b.snd ≤ a.size ∧
   -       (b.fst = true ↔ ∀ j, j < b.snd → a[j]! < n)) ∧
   -       a.size ≤ b.snd
   - · fun b => a.size - b.snd -/
  vcgen_ [isGreaterWithInvariants] simplifying_assumptions with try finish
  all_goals sorry

  /- vcgen' [isGreaterWithInvariants] <;> try grind
   - · split_conjs; constructor
   -   · grind
   -   · next b h hbranch left right =>
   -       intro hall
   -       exfalso
   -       apply hbranch
   -       have hlt := hall b.snd (by omega)
   -       simpa [getElem!_pos, h] using hlt -/
  


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
  all_goals grind

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
  vcgen_ [isGreaterInlineAnnotations]
  all_goals grind

/- A finite range using Velvet's `for'` annotations and the bundled VCGen frontend. -/
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
  vcgen_ [scanRangeVCGen]

method isGreaterWithInvariants' (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let res <- isGreaterWithInvariants n a
  return res



prove_correct isGreaterWithInvariants' by
  vcgen'' [isGreaterWithInvariants'] 
  --constructor
  --intros; grind
  --intros; expose_names
  --have h' := h i (by grind)
  --grind

#check isGreaterWithInvariants_correct

run_meta do
    let isRec <- Lean.Meta.isRecursiveDefinition `isGreaterWithInvariants
    dbg_trace s!"{isRec}"


method rec foo' (p: Int)
returns (res: Int) 
requires True
ensures True do
    let res <- foo' (p-1)
    return res

-- Should this really verify?? Very weirddd (even when I change Int -> Nat)
prove_correct foo' by
  vcgen'' [foo']
  

method get_idx returns (res: Nat)
    ensures res = 1
    do
        return 1

prove_correct get_idx by
  vcgen'' [get_idx] with finish


method isGreaterWithInvariants'' (n : Int) (a : Array Int)
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

prove_correct isGreaterWithInvariants'' by
    vcgen'' [isGreaterWithInvariants'']
    all_goals sorry

