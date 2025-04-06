import LoL.MProp.Instances
import LoL.MProp.NonDetT

import LoL.Meta

set_option autoImplicit true

namespace Veil


abbrev ExecDet (σ ρ : Type) := ExceptT String (StateT σ Id) ρ
abbrev Exec (σ ρ : Type) := NonDetT (ExecDet σ) ρ

-- #gen_spec assertE' (σ α : Type) for
--   wp (m := ExecDet σ) (α := α) (StateT.lift (.mk (.error "assertion failed")))
open TotalCorrectness in
#gen_spec Total.getE (σ : Type) for wp (liftM (m := StateT σ Id) (n :=  ExecDet σ) (StateT.get))
open TotalCorrectness in
#gen_spec Total.setE (σ : Type) (s : σ) for wp (liftM (m := StateT σ Id) (n :=  ExecDet σ) (StateT.set s))
open PartialCorrectness in
#gen_spec Partial.getE (σ : Type) for wp (liftM (m := StateT σ Id) (n :=  ExecDet σ) (StateT.get))
open PartialCorrectness in
#gen_spec Partial.setE (σ : Type) (s : σ) for wp (liftM (m := StateT σ Id) (n :=  ExecDet σ) (StateT.set s))



lemma iInfE : iInf (α := σ -> Prop) f = fun x => ∀ y, f y x := by ext; simp
lemma iSupE : iSup (α := σ -> Prop) f = fun x => ∃ y, f y x := by ext; simp
lemma complE : (fᶜ : σ -> Prop) = fun x => ¬ f x := by ext; simp

lemma topE : (⊤ : σ -> Prop) = fun _ => True := by rfl
lemma botE : (⊥ : σ -> Prop) = fun _ => False := by rfl
@[simp]
lemma if_fun [Decidable cnd] (tf ef : α -> β) :
  (if cnd then fun x => tf x else fun x => ef x) = fun x => if cnd then tf x else ef x := by
  split_ifs <;> rfl
@[wpSimp]
lemma if_app {α β} p [Decidable p] (t e : α -> β)  : (if p then t else e) = fun x => if p then t x else e x := by
  split <;> rfl
@[simp]
lemma not_if {_ : Decidable p} (t e : Prop) : (¬ (if p then t else e)) = if p then ¬ t else ¬ e := by
  split_ifs <;> simp

def assert (as : Prop) [Decidable as] [Monad m] [MonadExcept String m] : m Unit := do
  do unless as do throw "assertion failed"


lemma assertE {σ} (as : Prop) [Decidable as] :
  assert (m := Exec σ) as = liftM (assert (m := ExecDet σ) as) := by sorry

lemma pureE {σ ρ} (x : ρ) :
  pure (f := Exec σ) x = NonDetT.pure x := rfl

section
-- open Demonic
-- namespace Demonic

open Demonic TotalCorrectness in
@[wpSimp]
lemma wpAssertE [Decidable as] :
  wp (assert (m := Exec σ) as) post = fun s => as ∧ post .unit s := by
    simp [assertE, NonDetT.wp_lift]
    simp [assert]; split_ifs <;> try simp [wpSimp, wp_pure]
    { ext s; constructor <;> simp_all }
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk]
    erw [wp_tot_eq, wp_pure]; simp_all; rfl

open Demonic PartialCorrectness in
@[wpSimp]
lemma PartialD.wpAssertE [Decidable as] :
  wp (assert (m := Exec σ) as) post = fun s => as -> post .unit s := by
    simp [assertE, NonDetT.wp_lift]
    simp [assert]; split_ifs <;> try simp [wpSimp, wp_pure]
    { ext s; constructor <;> simp_all }
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk]
    erw [wp_part_eq, wp_pure]; simp_all; rfl

open Angelic TotalCorrectness in
@[wpSimp]
lemma wpAssertEA [Decidable as] :
  wp (assert (m := Exec σ) as) post = fun s => as ∧ post .unit s := by
    simp [assertE, NonDetT.wp_lift]
    simp [assert]; split_ifs <;> try simp [wpSimp, wp_pure]
    { ext s; constructor <;> simp_all }
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk]
    erw [wp_tot_eq, wp_pure]; simp_all; rfl

open Angelic PartialCorrectness in
@[wpSimp]
lemma PartialD.wpAssertEA [Decidable as] :
  wp (assert (m := Exec σ) as) post = fun s => as -> post .unit s := by
    simp [assertE, NonDetT.wp_lift]
    simp [assert]; split_ifs <;> try simp [wpSimp, wp_pure]
    { ext s; constructor <;> simp_all }
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk]
    erw [wp_part_eq, wp_pure]; simp_all; rfl

open Demonic TotalCorrectness in
@[wpSimp]
lemma Total.wpGetE :
  wp (get (m := Exec σ)) post = fun s => post s s := by
    ext s; simp only [get, getThe, MonadStateOf.get, @NonDetT.wp_lift, wpSimp]

open Demonic PartialCorrectness in
@[wpSimp]
lemma PartialD.wpGetE :
  wp (get (m := Exec σ)) post = fun s => post s s := by
    ext s; simp only [get, getThe, MonadStateOf.get, @NonDetT.wp_lift, wpSimp]

open Angelic TotalCorrectness in
@[wpSimp]
lemma TotalA.wpGetE :
  wp (get (m := Exec σ)) post = fun s => post s s := by
    ext s; simp only [get, getThe, MonadStateOf.get, @NonDetT.wp_lift, wpSimp]

open Angelic PartialCorrectness in
@[wpSimp]
lemma PartialA.wpGetE :
  wp (get (m := Exec σ)) post = fun s => post s s := by
    ext s; simp only [get, getThe, MonadStateOf.get, @NonDetT.wp_lift, wpSimp]


open Demonic TotalCorrectness in
@[wpSimp]
lemma Total.wpSetE :
  wp (set (σ := σ) (m := Exec σ) s) post = fun _ => post .unit s := by
    ext s; simp only [set, MonadStateOf.set, NonDetT.wp_lift, wpSimp]

open Demonic PartialCorrectness in
@[wpSimp]
lemma Partial.wpSetE :
  wp (set (σ := σ) (m := Exec σ) s) post = fun _ => post .unit s := by
    ext s; simp only [set, MonadStateOf.set, NonDetT.wp_lift, wpSimp]

open Angelic TotalCorrectness in
@[wpSimp]
lemma TotalA.wpSetE :
  wp (set (σ := σ) (m := Exec σ) s) post = fun _ => post .unit s := by
    ext s; simp only [set, MonadStateOf.set, NonDetT.wp_lift, wpSimp]

open Angelic PartialCorrectness in
@[wpSimp]
lemma PartialA.wpSetE :
  wp (set (σ := σ) (m := Exec σ) s) post = fun _ => post .unit s := by
    ext s; simp only [set, MonadStateOf.set, NonDetT.wp_lift, wpSimp]


open Demonic TotalCorrectness in
@[wpSimp]
lemma Total.wp_if (p : Prop) [Decidable p] (t e : Exec σ α) :
  wp (if p then t else e) post = fun s => if p then wp t post s else wp e post s := by
    unfold wp; split_ifs <;> rfl

open Demonic PartialCorrectness in
@[wpSimp]
lemma Partial.wp_if (p : Prop) [Decidable p] (t e : Exec σ α) :
  wp (if p then t else e) post = fun s => if p then wp t post s else wp e post s := by
    unfold wp; split_ifs <;> rfl

-- end Demonic
end



variable {σ ρ : Type}

def nonDet : Exec Nat Unit := do
  let b₁ <- pick Bool
  let b₂ <- pick Bool
  if b₁ then
    if b₂ then
      assert False
    else
      set ((<-get) + 1)
  else
    if b₂ then
      assume False
    else
      set ((<-get) - 1)

example (P : _ -> Prop) : P nonDet.finally := by
  simp only [nonDet, NonDetT.ite_eq, assertE, pureE]
  dsimp [bind, NonDetT.pure, NonDetT.finally]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  unfold NonDetT.ite; dsimp
  simp [pick_tpc,
        assume_tpc,
        lift_tpc,
        assume_pre,
        lift_pre,
        lift_sem,
        pick_sem,
        pick_pre,
        wp_pure,
        assume_sem,
        Id, bind_pure
        ]
  unfold pick; simp [instMonadNonDetNonDetT, NonDetT.pick]
  sorry

section
open Demonic

attribute [wpSimp] wp_bind MonadNonDet.wp_pick MonadNonDet.wp_assume

open TotalCorrectness in
example (P : _ -> Prop) : P (wp nonDet post) := by
  simp [nonDet, -NonDetT.ite_eq, wpSimp, iInfE]
  sorry

open PartialCorrectness in
example (P : _ -> Prop) : P (wp nonDet post) := by
  simp [nonDet, -NonDetT.ite_eq, wpSimp, iInfE]
  sorry


end

section
open Angelic

attribute [wpSimp] wp_bind MonadNonDet.wp_pick MonadNonDet.wp_assume

section
open TotalCorrectness
example (P : _ -> Prop) : P (wp nonDet post) := by
  simp [nonDet, -NonDetT.ite_eq, wpSimp, iSupE]
  sorry

def tr (c : Exec σ α) (s s' : σ) (r' : α) := wp c (· = r' ∧ · = s') s

example (P : _ -> Prop) : P (tr nonDet s s') := by
  unfold tr
  simp [nonDet, -NonDetT.ite_eq, wpSimp, iSupE]
  sorry

end

open PartialCorrectness in
example (P : _ -> Prop) : P (wp nonDet post) := by
  simp [nonDet, -NonDetT.ite_eq, wpSimp, iSupE]
  sorry


end

end Veil
