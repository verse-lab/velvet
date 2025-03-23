import LoL.MProp.EffectObservations
import LoL.NonDetM

instance : Nonempty PProp := ⟨PProp.mk True⟩

instance : MPropPartialOrder Id Prop where
  μ := (·.prop)
  ι := fun x => PProp.mk x
  μ_surjective := by simp [Function.LeftInverse]
  μ_pure_injective := by simp
  μ_top := by simp
  μ_bot := by simp
  μ_nontriv := by simp
  μ_ord_pure := by simp
  μ_ord_bind := by solve_by_elim

instance : MPropDetertministic Id Prop where
  demonic := by
    intros α c p q;
    simp [MProp.lift, MProp.ι, MProp.μ_surjective, MProp.μ, MPropPartialOrder.ι, MPropPartialOrder.μ]
  angelic := by
    intros α c p q;
    simp [MProp.lift, MProp.ι, MProp.μ_surjective, MProp.μ, MPropPartialOrder.ι, MPropPartialOrder.μ]


instance (σ : Type) (l : Type) (m : Type -> Type)
  [Inhabited σ]
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (StateT σ m) (σ -> l) where
  μ := fun sp s => Prod.fst <$> sp s |> inst.μ
  μ_top := by intros x s; simp [pure, StateT.pure]; apply inst.μ_top
  μ_bot := by intros x s; simp [pure, StateT.pure]; apply inst.μ_bot
  ι := fun sp s => (·, s) <$> MProp.ι (sp s)
  μ_surjective := by intro x; simp [funext_iff]; intro s; apply inst.μ_surjective
  μ_pure_injective := by
    simp [pure, StateT.pure, MProp.ι, inst.μ_pure_injective]; intro p; rfl
  μ_ord_pure := by
    intros p₁ p₂ imp s; simp [pure, StateT.pure]
    solve_by_elim [MPropPartialOrder.μ_ord_pure]
  μ_nontriv := by
    simp [pure, StateT.pure, funext_iff];
    solve_by_elim [MPropPartialOrder.μ_nontriv]
  μ_ord_bind := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x s
    have leM := @inst.μ_ord_bind (α × σ) (fun as => Prod.fst <$> f as.1 as.2) (fun as => Prod.fst <$> g as.1 as.2)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; simp only [implies_true, le]

instance (σ : Type) (l : Type) (m : Type -> Type)
  [Inhabited σ]
  [Lattice l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] [inst': MPropDetertministic m l]
   : MPropDetertministic (StateT σ m) (σ -> l) where
    demonic := by
      intros α c p q s;
      simp [MProp.lift, MProp.μ, MPropPartialOrder.μ]
      simp [bind, StateT.bind]; simp [MProp.ι, MPropPartialOrder.ι]
      have h := inst'.demonic (α := α × σ) (c := c s) (p := fun x => p x.1 x.2) (q := fun x => q x.1 x.2)
      simp [MProp.lift, MProp.ι, MProp.μ] at h
      apply h
    angelic := by
      intros α c p q s;
      simp [MProp.lift, MProp.μ, MPropPartialOrder.μ]
      simp [bind, StateT.bind]; simp [MProp.ι, MPropPartialOrder.ι]
      have h := inst'.angelic (α := α × σ) (c := c s) (p := fun x => p x.1 x.2) (q := fun x => q x.1 x.2)
      simp [MProp.lift, MProp.ι, MProp.μ] at h
      apply h

instance (ρ : Type) (l : Type) (m : Type -> Type)
  [Inhabited ρ]
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (ReaderT ρ m) (ρ -> l) where
  μ := fun rp r => rp r |> inst.μ
  ι := fun rp r => MProp.ι (rp r)
  μ_surjective := by
    intro x; simp [funext_iff];
    intro r; apply inst.μ_surjective
  μ_pure_injective := by
    simp [MProp.ι, pure, ReaderT.pure, inst.μ_pure_injective]
    intro p; rfl
  μ_top := by intros x s; simp [pure]; apply inst.μ_top
  μ_bot := by intros x s; simp [pure]; apply inst.μ_bot
  μ_ord_pure := by
    intros p₁ p₂ imp s; simp [pure]
    solve_by_elim [MPropPartialOrder.μ_ord_pure]
  μ_nontriv := by
    simp [pure, ReaderT.pure, funext_iff];
    solve_by_elim [MPropPartialOrder.μ_nontriv]
  μ_ord_bind := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x r
    have leM := @inst.μ_ord_bind α (f · r) (g · r)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; simp only [implies_true, le]

instance (σ : Type) (l : Type) (m : Type -> Type)
  [Inhabited σ]
  [Lattice l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] [inst': MPropDetertministic m l]
   : MPropDetertministic (ReaderT σ m) (σ -> l) where
  demonic := by
      intros α c p q s;
      simp [MProp.lift, MProp.μ, MPropPartialOrder.μ]
      simp [bind, ReaderT.bind]
      simp [MProp.ι, MProp.μ_surjective, MPropPartialOrder.μ_surjective]
      have h := inst'.demonic (α := α) (c := c s) (p := fun x => p x s) (q := fun x => q x s)
      simp [MProp.lift, MProp.ι, MProp.μ, MProp.μ_surjective] at h
      apply h
  angelic := by
      intros α c p q s;
      simp [MProp.lift, MProp.μ, MPropPartialOrder.μ]
      simp [bind, ReaderT.bind]
      simp [MProp.ι, MProp.μ_surjective, MPropPartialOrder.μ_surjective]
      have h := inst'.angelic (α := α) (c := c s) (p := fun x => p x s) (q := fun x => q x s)
      simp [MProp.lift, MProp.ι, MProp.μ, MProp.μ_surjective] at h
      apply h

abbrev Except.getD {ε α} (default : α)  : Except ε α -> α
  | Except.ok p => p
  | Except.error _ => default

abbrev Except.bind' {m : Type -> Type} {ε α β} [Monad m] : Except ε α -> (α -> ExceptT ε m β) -> ExceptT ε m β :=
  fun x f => bind (m := ExceptT ε m) (pure (f := m) x) f

lemma Except.bind'_bind {m : Type -> Type} {ε α β} [Monad m] [LawfulMonad m] (i : m (Except ε α)) (f : α -> ExceptT ε m β) :
  (i >>= fun a => Except.bind' a f) = bind (m := ExceptT ε m) i f := by
  simp [Except.bind', bind, bind_assoc, ExceptT.bind]; rfl

def MPropExcept (df : Prop) (ε : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (ExceptT ε m) l where
  μ := fun e => inst.μ $ Except.getD df <$> e
  μ_top := by intros x; simp [pure, ExceptT.pure, ExceptT.mk]; apply inst.μ_top
  μ_bot := by intros x; simp [pure, ExceptT.pure, ExceptT.mk]; apply inst.μ_bot
  ι := fun x => Functor.map (β := Except _ _) .ok (MProp.ι x)
  μ_surjective := by
    intro x; simp [funext_iff]; apply inst.μ_surjective
  μ_pure_injective := by
    simp [pure, ExceptT.pure, ExceptT.mk, MProp.ι, inst.μ_pure_injective]
  μ_nontriv := by
    simp [pure, ExceptT.pure, Except.getD, ExceptT.mk, funext_iff];
    solve_by_elim [MPropPartialOrder.μ_nontriv]
  μ_ord_pure := by
    intros p₁ p₂ imp; simp [pure, ExceptT.pure, ExceptT.mk]
    solve_by_elim [MPropPartialOrder.μ_ord_pure]
  μ_ord_bind := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x
    have leM := @inst.μ_ord_bind (Except ε α)
      (fun x => Except.getD df <$> Except.bind' x f)
      (fun x => Except.getD df <$> Except.bind' x g)
    simp only [Function.comp, Pi.hasLe, <-map_bind, Except.bind'_bind] at leM
    apply leM; rintro (e | p) <;> simp [Except.bind', ExceptT.instMonad, ExceptT.bind, ExceptT.bindCont]
    apply le

namespace PartialCorrectness
scoped
instance (ε : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (ExceptT ε m) l := MPropExcept True ε l m

def MPropExceptDetertministic (ε : Type) (l : Type) (m : Type -> Type)
  [Lattice l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l]
  [inst': MPropDetertministic m l] : MPropDetertministic (ExceptT ε m) l where
  demonic := by
    intros α c p q
    simp [MProp.lift, MProp.μ, MPropPartialOrder.μ]
    simp [bind, ExceptT.bind, ExceptT.mk]; unfold ExceptT.bindCont
    simp [MProp.ι, MPropPartialOrder.ι]
    simp [instMPropPartialOrderExceptTOfLawfulMonad, MPropExcept, MProp.ι]
    have h := inst'.demonic (α := Except ε α) (c := c)
      (p := fun e =>
        match e with
        | Except.ok a    => p a
        | Except.error e => ⌜True⌝ )
      (q := fun e =>
        match e with
        | Except.ok a    => q a
        | Except.error e => ⌜True⌝ )
    simp [MProp.lift, MProp.ι, MProp.μ, MProp.μ_surjective] at h
    have h₁ : ∀ p : α -> l,
      (do
        bind (m := m) c fun a =>
        Except.getD { prop := True } <$>
            match a with
            | Except.ok a => Except.ok <$> MPropPartialOrder.ι (p a)
            | Except.error e => pure (Except.error e)) =
      (do
        bind (m := m) c fun a =>
        (MPropPartialOrder.ι $ match a with
            | Except.ok a =>  (p a)
            | Except.error e => ⌜True⌝)) := by
      intro p; congr; ext a; cases a <;> simp
      simp [Except.getD, MProp.pure, MProp.μ, inst.μ_pure_injective]
    (repeat erw [h₁]); clear h₁; apply le_trans; apply h
    apply le_of_eq; congr; ext a; cases a <;> simp
  angelic := by
    intros α c p q
    simp [MProp.lift, MProp.μ, MPropPartialOrder.μ]
    simp [bind, ExceptT.bind, ExceptT.mk]; unfold ExceptT.bindCont
    simp [MProp.ι, MPropPartialOrder.ι]
    simp [instMPropPartialOrderExceptTOfLawfulMonad, MPropExcept, MProp.ι]
    have h := inst'.angelic (α := Except ε α) (c := c)
      (p := fun e =>
        match e with
        | Except.ok a    => p a
        | Except.error e => ⌜True⌝ )
      (q := fun e =>
        match e with
        | Except.ok a    => q a
        | Except.error e => ⌜True⌝ )
    simp [MProp.lift, MProp.ι, MProp.μ, MProp.μ_surjective] at h
    have h₁ : ∀ p : α -> l,
      (do
        bind (m := m) c fun a =>
        Except.getD { prop := True } <$>
            match a with
            | Except.ok a => Except.ok <$> MPropPartialOrder.ι (p a)
            | Except.error e => pure (Except.error e)) =
      (do
        bind (m := m) c fun a =>
        (MPropPartialOrder.ι $ match a with
            | Except.ok a =>  (p a)
            | Except.error e => ⌜True⌝)) := by
      intro p; congr; ext a; cases a <;> simp
      simp [Except.getD, MProp.pure, MProp.μ, inst.μ_pure_injective]
    (repeat erw [h₁]); clear h₁; apply le_trans'; apply h
    apply le_of_eq; congr; ext a; cases a <;> simp


end PartialCorrectness

namespace TotalCorrectness
scoped
instance (ε : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (ExceptT ε m) l := MPropExcept False ε l m

def MPropExceptDetertministic (ε : Type) (l : Type) (m : Type -> Type)
  [Lattice l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l]
  [inst': MPropDetertministic m l] : MPropDetertministic (ExceptT ε m) l where
  demonic := by
    intros α c p q
    simp [MProp.lift, MProp.μ, MPropPartialOrder.μ]
    simp [bind, ExceptT.bind, ExceptT.mk]; unfold ExceptT.bindCont
    simp [MProp.ι, MPropPartialOrder.ι]
    simp [instMPropPartialOrderExceptTOfLawfulMonad, MPropExcept, MProp.ι]
    have h := inst'.demonic (α := Except ε α) (c := c)
      (p := fun e =>
        match e with
        | Except.ok a    => p a
        | Except.error e => ⌜False⌝ )
      (q := fun e =>
        match e with
        | Except.ok a    => q a
        | Except.error e => ⌜False⌝ )
    simp [MProp.lift, MProp.ι, MProp.μ, MProp.μ_surjective] at h
    have h₁ : ∀ p : α -> l,
      (do
        bind (m := m) c fun a =>
        Except.getD { prop := False } <$>
            match a with
            | Except.ok a => Except.ok <$> MPropPartialOrder.ι (p a)
            | Except.error e => pure (Except.error e)) =
      (do
        bind (m := m) c fun a =>
        (MPropPartialOrder.ι $ match a with
            | Except.ok a =>  (p a)
            | Except.error e => ⌜False⌝)) := by
      intro p; congr; ext a; cases a <;> simp
      simp [Except.getD, MProp.pure, MProp.μ, inst.μ_pure_injective]
    (repeat erw [h₁]); clear h₁; apply le_trans; apply h
    apply le_of_eq; congr; ext a; cases a <;> simp
  angelic := by
    intros α c p q
    simp [MProp.lift, MProp.μ, MPropPartialOrder.μ]
    simp [bind, ExceptT.bind, ExceptT.mk]; unfold ExceptT.bindCont
    simp [MProp.ι, MPropPartialOrder.ι]
    simp [instMPropPartialOrderExceptTOfLawfulMonad, MPropExcept, MProp.ι]
    have h := inst'.angelic (α := Except ε α) (c := c)
      (p := fun e =>
        match e with
        | Except.ok a    => p a
        | Except.error e => ⌜False⌝ )
      (q := fun e =>
        match e with
        | Except.ok a    => q a
        | Except.error e => ⌜ False ⌝ )
    simp [MProp.lift, MProp.ι, MProp.μ, MProp.μ_surjective] at h
    have h₁ : ∀ p : α -> l,
      (do
        bind (m := m) c fun a =>
        Except.getD { prop := False } <$>
            match a with
            | Except.ok a => Except.ok <$> MPropPartialOrder.ι (p a)
            | Except.error e => pure (Except.error e)) =
      (do
        bind (m := m) c fun a =>
        (MPropPartialOrder.ι $ match a with
            | Except.ok a =>  (p a)
            | Except.error e => ⌜ False ⌝)) := by
      intro p; congr; ext a; cases a <;> simp
      simp [Except.getD, MProp.pure, MProp.μ, inst.μ_pure_injective]
    (repeat erw [h₁]); clear h₁; apply le_trans'; apply h
    apply le_of_eq; congr; ext a; cases a <;> simp


end TotalCorrectness

#guard_msgs (drop info) in
#synth MPropPartialOrder (StateM Int) (Int -> Prop)

#guard_msgs (drop info) in
#synth MPropPartialOrder (ReaderT Bool (StateM Int)) (Bool -> Int -> Prop)


namespace AngelicChoice

instance NonDetMProp :
   MPropPartialOrder NonDetM.{0} Prop where
  μ := (∃ x ∈ ·.takeAll, x.prop)
  ι := (NonDetM.one ·)
  μ_surjective := by
    intros x; simp [NonDetM.takeAll]
  μ_pure_injective := by
    simp [pure, NonDetM.takeAll]
  μ_top := by intros x; simp [pure, NonDetM.takeAll]
  μ_bot := by intros x; simp [pure, NonDetM.takeAll]
  μ_nontriv := by simp [pure, NonDetM.takeAll]
  μ_ord_pure := by
    intros p₁ p₂ imp; simp [pure, NonDetM.takeAll]
    solve_by_elim
  μ_ord_bind := by
    intros α f g le x; simp; induction x <;> simp_all [bind, NonDetM.bind, NonDetM.takeAll, NonDetM.takeAll_union]
    rename_i y _ ih; rintro x (h|h) xp
    · specialize le y ?_; simp; exists x
      rcases le with ⟨z, _, _⟩; exists z; simp [*]
    specialize ih () x ?_ ?_ <;> try assumption
    rcases ih with ⟨z, _, _⟩; exists z; simp [*]

end AngelicChoice

namespace DemonicChoice

abbrev List.forall {α} (f : α -> Prop) : List α -> Prop
  | [] => True
  | x :: xs => f x ∧ List.forall f xs

@[simp]
theorem List.forall_forall {α} (f : α -> Prop) (xs : List α) : List.forall f xs ↔ ∀ x ∈ xs, f x := by
  induction xs <;> simp [List.forall, *]

instance NonDetMProp :
   MPropPartialOrder NonDetM.{0} Prop where
  μ := (List.forall (·.prop) ·.takeAll)
  ι := (NonDetM.one ·)
  μ_surjective := by
    intros x; simp [NonDetM.takeAll]
  μ_pure_injective := by
    simp [pure, NonDetM.takeAll]
  μ_top := by intros x; simp [pure, NonDetM.takeAll]
  μ_bot := by intros x; simp [pure, NonDetM.takeAll]
  μ_nontriv := by simp [pure, NonDetM.takeAll]
  μ_ord_pure := by
    intros p₁ p₂ imp; simp [pure, NonDetM.takeAll]
    solve_by_elim
  μ_ord_bind := by
    intros α f g le x; simp; induction x <;> simp_all [bind, NonDetM.bind, NonDetM.takeAll, NonDetM.takeAll_union]
    rename_i y _ ih; rintro h x (hh|hh);
    · specialize le y ?_ _ hh <;> simp_all
    specialize ih () ?_
    · intros; apply h; simp [*]
    solve_by_elim

end DemonicChoice
