import Mathlib.Order.Basic

universe u v w

class MonadTransformer (t : (Type u -> Type v) -> (Type u -> Type w)) where
  isMonad {m} [Monad m] : Monad (t m)
  monadLiftT {m} [Monad m] : {α : Type u} -> m α -> t m α
  monadMapT {m n} [Monad m] [Monad n] [inst : MonadLiftT m n] {α : Type u} : t m α -> t n α
  monad_map_lift {m n} [Monad m] [Monad n] [MonadLiftT m n] {α : Type u} (x : m α) :
    (monadMapT $ monadLiftT x) = (monadLiftT $ monadLift (n := n) x)

export MonadTransformer (monadLiftT monadMapT)

instance (t : (Type u -> Type v) -> (Type u -> Type w)) (m : Type u -> Type v) [MonadTransformer t] [Monad m] :
  Monad (t m) := MonadTransformer.isMonad

instance (t : (Type u -> Type v) -> (Type u -> Type w)) [MonadTransformer t] (m : Type u -> Type v) [Monad m] :
  MonadFunctor m (t m) where
   monadMap := fun f => monadMapT (inst := ⟨f⟩)

abbrev Cont (t : Type v) (α : Type u) := (α -> t) -> t

instance (t : Type v) : Monad (Cont t) where
  pure x := fun f => f x
  bind x f := fun g => x (fun a => f a g)

@[simp]
def Cont.monotone {t : Type v} {α : Type u} [Preorder t] (wp : Cont t α) :=
  ∀ (f f' : α -> t), (∀ a, f a ≤ f' a) → wp f ≤ wp f'

structure W (t : Type v) [Preorder t] (α : Type u) where
  wp : Cont t α
  wp_montone : wp.monotone

@[ext]
lemma W_ext (t : Type v) (α : Type u) [Preorder t] (w w' : W t α) :
  w.wp = w'.wp → w = w' := by intros; cases w; cases w'; simp_all

instance (t : Type v) [Preorder t] : Monad (W t) where
  pure x := ⟨fun f => f x, by solve_by_elim⟩
  bind x f := ⟨fun g => x.wp (fun a => (f a).wp g), by simp; intros; solve_by_elim [W.wp_montone]⟩

class Logic (t : Type u) extends PartialOrder t where
  and : t -> t -> t
  pure : Prop -> t
