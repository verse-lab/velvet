import LoL.MProp.EffectObservations
import LoL.NonDetT

instance : Nonempty PProp := ⟨PProp.mk True⟩

instance : MPropPartialOrder Id Prop where
  μ := (·.prop)
  μSur := by exists (fun x => PProp.mk x); simp [Function.LeftInverse]
  μOrd := by solve_by_elim

instance (σ : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (StateT σ m) (σ -> l) where
  μ := fun sp s => Prod.fst <$> sp s |> inst.μ
  μSur := by
    exists fun sp s => (·, s) <$> MProp.ι (sp s)
    intro x; simp [funext_iff];
    intro s; apply inst.μSur.property
  μOrd := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x s
    have leM := @inst.μOrd (α × σ) (fun as => Prod.fst <$> f as.1 as.2) (fun as => Prod.fst <$> g as.1 as.2)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; simp only [implies_true, le]

instance (ρ : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (ReaderT ρ m) (ρ -> l) where
  μ := fun rp r => rp r |> inst.μ
  μSur := by
    exists fun rp r => MProp.ι (rp r)
    intro x; simp [funext_iff];
    intro r; apply inst.μSur.property
  μOrd := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x r
    have leM := @inst.μOrd α (f · r) (g · r)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; simp only [implies_true, le]


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
  μSur := by
    exists fun x => Functor.map (β := Except _ _) .ok (MProp.ι x)
    intro x; simp [funext_iff]; apply inst.μSur.property
  μOrd := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x
    have leM := @inst.μOrd (Except ε α)
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
end PartialCorrectness

namespace TotalCorrectness
scoped
instance (ε : Type) (l : Type) (m : Type -> Type)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropPartialOrder m l] : MPropPartialOrder (ExceptT ε m) l := MPropExcept False ε l m
end TotalCorrectness

#guard_msgs (drop info) in
#synth MPropPartialOrder (StateM Int) (Int -> Prop)

#guard_msgs (drop info) in
#synth MPropPartialOrder (ReaderT Bool (StateM Int)) (Bool -> Int -> Prop)


namespace AngelicChoice

instance NonDetMProp :
   MPropPartialOrder NonDetM.{0} Prop where
  μ := (∃ x ∈ ·.takeAll, x.prop)
  μSur := by
    exists (NonDetM.one ·); intros x; simp [NonDetM.takeAll]
  μOrd := by
    intros α f g le x; simp; induction x <;> simp_all [bind, NonDetM.bind, NonDetM.takeAll, NonDetM.takeAll_union]
    rename_i y _ ih; rintro x (h|h) xp
    · specialize le y ?_; simp; exists x
      rcases le with ⟨z, _, _⟩; exists z; simp [*]
    specialize ih () x ?_ ?_ <;> try assumption
    rcases ih with ⟨z, _, _⟩; exists z; simp [*]

end AngelicChoice

namespace DemonicChoice

instance NonDetMProp :
   MPropPartialOrder NonDetM.{0} Prop where
  μ := (∀ x ∈ ·.takeAll, x.prop)
  μSur := by
    exists (NonDetM.one ·); intros x; simp [NonDetM.takeAll]
  μOrd := by
    intros α f g le x; simp; induction x <;> simp_all [bind, NonDetM.bind, NonDetM.takeAll, NonDetM.takeAll_union]
    rename_i y _ ih; rintro h x (hh|hh);
    · specialize le y ?_ _ hh <;> simp_all
    specialize ih () ?_
    · intros; apply h; simp [*]
    solve_by_elim

end DemonicChoice
