import Mathlib.Order.Basic

universe u v w

variable (m : Type u -> Type w) (w : Type u -> Type v)

class PreOrderFunctor  where preord : (α : Type u) -> Preorder (w α)
instance [inst: (α : Type u) -> Preorder (w α)] : PreOrderFunctor w := ⟨inst⟩
instance (α : Type u) [inst: PreOrderFunctor w] : Preorder (w α) := inst.preord α

class MonadOrder extends Monad w, PreOrderFunctor w where
  bind_le {α : Type u} {β : Type u} (x y : w α) (f g : α -> w β) :
    x ≤ y → (∀ a, f a ≤ g a) → bind x f ≤ bind y g

class LawfulMonadLift (w : outParam (Type u -> Type v)) [Monad m] [Monad w] extends MonadLiftT m w where
  monadMapPure {α : Type u} (x : α) : monadLift (pure x) = pure x
  monadMapBind {α : Type u} {β : Type u} (x : m α) (f : α -> m β) : monadLift (bind x f) = bind (monadLift x) (fun x => monadLift (f x))

export LawfulMonadLift (monadMapPure monadMapBind)

alias EffectObservation := LawfulMonadLift

class abbrev SpecMonad [Monad m] := MonadOrder w, LawfulMonadLift m w
