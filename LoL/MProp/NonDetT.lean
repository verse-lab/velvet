import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Aesop
import LoL.QuotientExtra
import LoL.Meta
import LoL.MProp.HoareTriples

universe u v w

section NonDetermenisticTransformer

variable {m : Type u -> Type v} {l : Type u} {α β : Type u} [Monad m] [inst: CompleteBooleanAlgebra l]

local
instance : SemilatticeInf l := inst.toLattice.toSemilatticeInf

variable  [MPropPartialOrder m l]

structure NonDetT (m : Type u -> Type v) (l : Type u)
  [Monad m] [CompleteBooleanAlgebra l] [MPropPartialOrder m l] [MPropDetertministic m l]
  (α : Type u) where
  tp   : Type w
  tp₀  : Inhabited tp
  pre  : tp -> l
  sem  : tp -> m α

@[simp]
lemma meet_pure_true l : min (MProp.pure (m := m) True) l = l := by simp
@[simp]
lemma pure_true_meet l : min l (MProp.pure (m := m) True) = l := by simp

variable [MPropDetertministic m l]

def NonDetT.pure (x : α) : NonDetT m l α :=
  ⟨PUnit, inferInstance, fun _ => MProp.pure (m := m) True, fun _ => return x⟩

def NonDetT.bind (x : NonDetT m l α) (f : α → NonDetT m l β) : NonDetT m l β :=
  ⟨
    x.tp × ((out : α) -> (f out).tp),
    by apply @instInhabitedProd _ _ x.tp₀ (@Pi.instInhabited _ _ (fun a => (f a).tp₀)),
    fun t => x.pre t.1 ⊓
      wlp (x.sem t.1) fun out => (f out).pre (t.2 out),
    fun t => x.sem t.1 >>= fun out => (f out).sem (t.2 out)
  ⟩

def NonDetT.pick (τ : Type u) [Inhabited τ] : NonDetT m l τ :=
  ⟨τ, inferInstance, fun _ => MProp.pure (m := m) True, Pure.pure⟩

def NonDetT.assume (as : Prop) : NonDetT m l PUnit :=
  ⟨PUnit, inferInstance, fun _ => MProp.pure (m := m) as, fun _ => return .unit⟩

instance : Monad (NonDetT m l) where
  pure := .pure
  bind := .bind

instance : MonadLift m (NonDetT m l) where
  monadLift := fun x => ⟨PUnit, inferInstance, fun _ => MProp.pure (m := m) True, fun _ => x⟩

class MonadInfNonDet (m : Type u → Type v) where
  pick : (τ : Type u) -> [Inhabited τ] → m τ
  assume : Prop → m PUnit

export MonadInfNonDet (pick assume)

instance : MonadInfNonDet (NonDetT m l) where
  pick   := .pick
  assume := .assume

theorem pick_tp (τ : Type u) [Inhabited τ] : (pick (m := NonDetT m l) τ).tp = τ := rfl
theorem pick_pre (τ : Type u) [Inhabited τ] : (pick (m := NonDetT m l) τ).pre = fun _ => MProp.pure (m := m) True := rfl
theorem assume_tp (as : Prop) : (assume (m := NonDetT m l) as).tp = PUnit := rfl
theorem assume_pre (as : Prop) : (assume (m := NonDetT m l) as).pre = fun _ => MProp.pure (m := m) as := rfl
theorem lift_tp {α : Type u} (x : m α) : (liftM (n := NonDetT m l) x).tp = PUnit := rfl
theorem lift_pre {α : Type u} (x : m α) : (liftM (n := NonDetT m l) x).pre = fun _ => MProp.pure (m := m) True := rfl
theorem lift_sem {α : Type u} (x : m α) : (liftM (n := NonDetT m l) x).sem = fun _ => x := rfl
theorem assume_sem (as : Prop) : (assume (m := NonDetT m l) as).sem = fun _ => return .unit := rfl
theorem pick_sem (τ : Type u) [Inhabited τ] : (pick (m := NonDetT m l) τ).sem = Pure.pure := rfl

def NonDetT.isMorphism {α : Type u} (x y : NonDetT m l α) (f : x.tp -> y.tp) : Prop :=
  (∀ t, x.pre t = y.pre (f t)) ∧
  ∀ t, x.sem t = y.sem (f t)

def NonDetT.hasMorphism {α : Type u} (x y : NonDetT m l α) : Prop :=
  ∃ f, x.isMorphism y f

theorem NonDetT.hasMorphism_refl {α : Type u} (x : NonDetT m l α) : x.hasMorphism x := by
  exists id
  constructor
  { intro t; simp }
  intro t; simp

theorem NonDetT.hasMorphism_trans {α : Type u} (x y z : NonDetT m l α) :
  x.hasMorphism y -> y.hasMorphism z -> x.hasMorphism z := by
  intro ⟨f, hxy⟩ ⟨g, hyz⟩
  exists g ∘ f
  constructor
  { intro t
    rw [hxy.1, hyz.1]; rfl }
  intro t
  rw [hxy.2, hyz.2]; rfl

theorem NonDetT.hasMorphism_bind {α β : Type u} (x y : NonDetT m l α) (f g : α -> NonDetT m l β) :
  x.hasMorphism y ->
  (∀ a, (f a).hasMorphism (g a)) ->
  (x.bind f).hasMorphism (y.bind g) := by
    rintro ⟨r, pre₁, sem₁⟩ r
    rcases Classical.skolem.mp r with ⟨fr, fbij⟩; clear r
    unfold NonDetT.bind
    exists fun a => ⟨r a.1, fun out => fr out $ a.2 out⟩
    unfold isMorphism at fbij ⊢; dsimp
    constructor <;> aesop

def NonDetT.equiv {α : Type u} (x y : NonDetT m l α) : Prop :=
  x.hasMorphism y ∧ y.hasMorphism x

theorem NonDetT.equiv_bind {α β : Type u} (x y : NonDetT m l α) (f g : α -> NonDetT m l β) :
  x.equiv y ->
  (∀ a, (f a).equiv (g a)) ->
  (x.bind f).equiv (y.bind g) := by
    rintro ⟨x2y, y2x⟩; unfold equiv; simp [forall_and]
    constructor <;> solve_by_elim [NonDetT.hasMorphism_bind]

theorem NonDetT.equiv_refl {α : Type u} (x : NonDetT m l α) : x.equiv x := by
  constructor <;> apply NonDetT.hasMorphism_refl

theorem NonDetT.equiv_symm {α : Type u} (x y : NonDetT m l α) : x.equiv y -> y.equiv x := by
  intro h
  constructor
  { exact h.2 }
  exact h.1

theorem NonDetT.equiv_trans {α : Type u} (x y z : NonDetT m l α) :
  x.equiv y -> y.equiv z -> x.equiv z := by
  rintro ⟨x2y, y2x⟩ ⟨y2z, z2y⟩
  constructor <;> apply NonDetT.hasMorphism_trans <;> assumption

theorem NonDetT.morphism_cancel {α : Type u} {x y : NonDetT m l α} {f : x.tp -> y.tp} {g : y.tp -> x.tp} :
  x.isMorphism y f -> y.isMorphism x g ->
  (∀ t : x.tp, x.sem (g (f t)) = x.sem t) ∧
  (∀ t : x.tp, x.pre (g (f t)) = x.pre t) := by
  rintro ⟨pred₁, sem₁⟩ ⟨pred₂, sem₂⟩
  simp [<-sem₁, <-sem₂, <-pred₂, <-pred₁]

def NonDetT.μ (x : NonDetT m l PProp) : l := ⨅ t : x.tp, x.pre t ⇨ MProp.μ (x.sem t)

theorem NonDetT.μ_equiv (x y : NonDetT m l PProp) : x.equiv y -> x.μ = y.μ := by
  rcases x with ⟨tp₁, pre₁, sem₁⟩
  rcases y with ⟨tp₂, pre₂, sem₂⟩
  rintro ⟨⟨f, semE₁, preE₁⟩, ⟨g, semE₂, preE₂⟩⟩
  simp at f g semE₁ semE₂ preE₁ preE₂ ⊢
  apply le_antisymm <;> apply sInf_le_sInf <;> (simp [Set.range]; intro x)
  { exists (g x); congr <;> simp [<-semE₂, preE₂] }
  exists (f x); congr <;> simp [<-semE₁, preE₁]

instance NonDetT.Setoid (α) : Setoid (NonDetT m l α) where
  r := NonDetT.equiv
  iseqv := {
    refl := equiv_refl
    symm := by exact fun {x y} ↦ equiv_symm x y
    trans := by exact fun {x y z} ↦ equiv_trans x y z }

lemma bind_eq (x y : NonDetT m l α) {f g : α → NonDetT m l β} :
  x ≈ y ->
  (∀ a, f a ≈ g a) ->
  (x.bind f) ≈ (y.bind g) := by apply NonDetT.equiv_bind

abbrev LawfullNonDetT m l
  [Monad m] [CompleteBooleanAlgebra l] [MPropPartialOrder m l] [MPropDetertministic m l] α :=
  Quotient (NonDetT.Setoid (m := m) α)

def η {α} {m : Type 1 -> Type} {l : Type}
  [Monad m] [Monad (fun t => m (PLift t))]
  [CompleteBooleanAlgebra l]
  [CompleteBooleanAlgebra (PLift l)]
  [MPropPartialOrder m (PLift l)]
  [MPropPartialOrder (fun t => m (PLift t)) l]
  [MPropDetertministic m (PLift l)]
  [MPropDetertministic (fun t => m (PLift t)) l] :
  NonDetT.{1, 0, 0} m (PLift l) (NonDetT.{0, 0, 0} (fun t => m (PLift t)) l α) -> NonDetT.{1, 0, 0} m (PLift l) (PLift α)
  | { tp, tp₀, pre, sem } => sorry
-- abbrev LawfullNonDetT.mk : NonDetT m l α -> LawfullNonDetT m l α := Quotient.mk (NonDetT.Setoid α)

def LawfullNonDetT.pure (x : α) : LawfullNonDetT m l α := ⟦NonDetT.pure x⟧

noncomputable def LawfullNonDetT.map
  (f : α → β)
  (x : LawfullNonDetT m l α)
  : LawfullNonDetT m l β :=
  Quotient.liftOn x (⟦f <$> ·⟧)
  (by
    intros; dsimp; apply Quotient.sound
    simp [Functor.map]; apply bind_eq <;> solve_by_elim [Setoid.refl])

noncomputable def LawfullNonDetT.bind
  (x : LawfullNonDetT m l α)
  (f : α → LawfullNonDetT m l β) : LawfullNonDetT m l β :=
  Quotient.liftOn x (⟦Quotient.liftOnFun f ·.bind⟧)
  (by intros; dsimp; apply Quotient.sound
      solve_by_elim [bind_eq, Quotient.liftOnFun_arg])

noncomputable
instance : Functor (LawfullNonDetT m l) where
  map := LawfullNonDetT.map

noncomputable
instance : Monad (LawfullNonDetT m l) where
  pure := LawfullNonDetT.pure
  bind := LawfullNonDetT.bind

@[simp]
lemma LawfullNonDetT.bind_quot : ∀ {α β} (x : NonDetT m l α) (f : α → NonDetT m l β),
  LawfullNonDetT.bind ⟦x⟧ (⟦f ·⟧) = ⟦x.bind f⟧ := by
    intros; unfold bind;
    apply Quotient.sound; transitivity
    apply Quotient.liftOnFun_correct
    intros; apply bind_eq <;> solve_by_elim [Setoid.refl]
    solve_by_elim [Setoid.refl]


open Classical in
instance [LawfulMonad m] : LawfulMonad (LawfullNonDetT m l) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_ (bind_pure_comp := ?_)
  { intros α x
    induction x using Quotient.ind
    rename_i nd; simp only [Functor.map, LawfullNonDetT.map, NonDetT.Setoid]
    simp only [Function.comp_id, Quotient.lift_mk, Quotient.eq]
    constructor
    { exists (·.1); rcases nd with ⟨tp, inh, pre, sem⟩
      simp [NonDetT.bind, NonDetT.pure];
      repeat' constructor <;> simp }
    exists (fun x => (x, fun _ => .unit))
    rcases nd with ⟨tp, inh, pre, sem⟩
    simp [NonDetT.bind, NonDetT.pure];
    repeat' constructor <;> simp }
  { intros α β x f; simp [pure, LawfullNonDetT.pure, bind]
    induction f using Quotient.fun_ind
    simp; simp [NonDetT.Setoid, NonDetT.pure, NonDetT.bind]
    rename_i nd; constructor
    { exists (·.2 x); constructor <;> simp }
    exists (fun ndx => (.unit,
      fun y =>
        if h : x = y then
          by rw [<-h]; refine ndx
        else (nd y).tp₀.default))
    constructor <;> simp }
  { intros α β γ x f g; simp [pure, LawfullNonDetT.pure, bind]
    induction x using Quotient.ind; rename_i ndx
    induction f using Quotient.fun_ind; rename_i ndf
    induction g using Quotient.fun_ind; rename_i ndg
    simp; simp [NonDetT.Setoid, NonDetT.pure, NonDetT.bind]
    constructor
    { exists (fun t => ⟨t.1.1, fun x => ⟨t.1.2 x, t.2⟩ ⟩)
      constructor <;> simp only [Prod.forall, implies_true]
      intro t ft₁ ft₂; rw [inf_assoc]; congr
      simp [wlp_bind, wlp_and] }
    unfold NonDetT.hasMorphism NonDetT.isMorphism; dsimp
    have f' : (out : β) → (ndg out).tp := sorry
    exists (fun t => ⟨⟨t.1, fun x => (t.2 x).1⟩, f'⟩ )
    simp only [Prod.forall]
    constructor
    { rintro t ft; simp [inf_assoc, wlp_bind, wlp_and]; congr 2
      ext a } }
  intros α β f x;
  simp [pure, LawfullNonDetT.pure, bind, Functor.map, LawfullNonDetT.map]
  induction x using Quotient.ind; rename_i ndx
  simp only [LawfullNonDetT.bind_quot, Quotient.lift_mk]; rfl




notation "NonDetT" t => NonDetT t _


end NonDetermenisticTransformer

section Example

open TotalCorrectness

abbrev myM := NonDetT (StateT Nat (ExceptT String Id))

def ex : myM Unit :=
  do
    set 0
    let x <- get
    assume (x < 1)


example (P : _ -> Prop) : P (ex) := by
  dsimp [ex, bind, pure]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp [pick_tp,
        assume_tp,
        lift_tp,
        assume_pred,
        lift_pred,
        lift_sem,
        assume_sem,
        -bind_pure_comp
        ]
  sorry

def ex' : myM Unit :=
  do
    let x <- pick ℕ
    let y <- pick ℕ
    assume (x < y)
    set (y - x)

example (P : _ -> Prop) : P (ex') := by
  dsimp [ex', bind, pure]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp only [pick_tp,
        assume_tp,
        lift_tp,
        assume_pred,
        lift_pred,
        lift_sem,
        pick_pred,
        pick_sem,
        assume_sem,
        wp_pure,
        meet_pure_true,
        pure_true_meet,
        ]
  sorry


def ex'' : myM Unit :=
  do
    let x <- pick ℕ
    assume (x < 1)
    let y <- pick ℕ
    let s <- get
    assume (y < s)
    set (y - x)

example (P : _ -> Prop) : P (ex'') := by
  dsimp [ex'', bind, pure]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp [pick_tp,
        assume_tp,
        lift_tp,
        assume_pred,
        lift_pred,
        lift_sem,
        pick_sem,
        pick_pred,
        wp_pure,
        assume_sem,
        meet_pure_true,
        pure_true_meet,
        ]
  sorry

#reduce! ex

end Example
