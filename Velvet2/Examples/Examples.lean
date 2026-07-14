import Velvet2.Syntax
import Velvet2.Ghost
import Velvet2.Tactics
import Velvet2.VCGen'.Driver

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

prove_correct isGreaterWithInvariants by
  vcgen'' [isGreaterWithInvariants]
  
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
      True
      (fun result => result = true ↔ ∀ i, i < a.size → a[i]! < n)
      True := by
  vcgen [isGreaterNativeWhile] invariants
  · fun
    | .inl b => 0 ≤ b.snd ∧ b.snd ≤ a.size ∧
        (b.fst = true ↔ ∀ j, j < b.snd → a[j]! < n)
    | .inr b => (0 ≤ b.snd ∧ b.snd ≤ a.size ∧
        (b.fst = true ↔ ∀ j, j < b.snd → a[j]! < n)) ∧
        a.size ≤ b.snd
  · fun b => a.size - b.snd
  all_goals simp only [Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  case vc1 => simp
  case vc2 =>
    rename_i result hinv
    rcases hinv with ⟨⟨_, hle, hok⟩, hge⟩
    have hi : result.snd = a.size := Nat.le_antisymm hle hge
    simpa [hi] using hok
  case vc3 =>
    rename_i state hinv hcond hbranch
    rcases hinv with ⟨_, _, hok⟩
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    rw [hok]
    constructor
    · intro hall j hj
      by_cases hlt : j < state.snd
      · exact hall j hlt
      · have : j = state.snd := by omega
        subst j
        exact hbranch
    · intro hall j hj
      exact hall j (by omega)
  case vc4 =>
    rename_i state hinv hcond hbranch
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    simp only [Bool.false_eq_true, false_iff]
    intro hall
    exact hbranch (hall state.snd (by omega))
  case vc5 =>
    rename_i state hinv hcond
    exact ⟨hinv, by omega⟩

method isGreaterWithInvariants' (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let res <- isGreaterWithInvariants n a
  return res



prove_correct isGreaterWithInvariants' by
  sorry
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
  sorry
  

method get_idx returns (res: Nat)
    ensures res = 1
    do
        return 1

prove_correct get_idx by
    sorry


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

/- prove_correct isGreaterWithInvariants'' by
 -     mvcgen' -/
