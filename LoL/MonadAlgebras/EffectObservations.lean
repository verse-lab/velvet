import LoL.MonadUtil
import LoL.SpecMonad

universe u v w

variable (m : Type u -> Type w)


class MonadAlgebra [Monad m] (x : outParam (Type u)) where
  morphism : m x -> x
  pure (y : x) : morphism (pure y) = y
  bind {α : Type u} (y : m α) (f : α -> m x) : morphism (y >>= f) = (morphism $ (morphism ∘ f) <$> y)

abbrev MonadAlgebra.lift {m} {t : Type u} [Monad m] [LawfulMonad m] [MonadAlgebra m t] :
  {α : Type u} -> m α -> Cont t α := fun x f => MonadAlgebra.morphism $ f <$> x

instance (t : Type u) [Monad m] [LawfulMonad m] [MonadAlgebra m t] : LawfulMonadLift m (Cont t) where
  monadLift := MonadAlgebra.lift
  monadMapPure := by intro α x; unfold MonadAlgebra.lift; simp [monadLift, pure, map_pure, MonadAlgebra.pure]
  monadMapBind := by intros α β x f; unfold MonadAlgebra.lift; ext g; simp [monadLift, bind, MonadAlgebra.bind]; rfl

class MonadAlgebraOrdered [Monad m] (x : outParam (Type u)) [Preorder x] extends MonadAlgebra m x where
  bind_le : ∀ {α : Type u} (y : m α) (f f' : α -> x),
    (∀ a, f a ≤ f' a) → morphism (f <$> y) ≤ morphism (f' <$> y)

lemma Cont.monotone_lift {t : Type u} [Monad m] [LawfulMonad m] [Preorder t] [MonadAlgebraOrdered m t] :
  ∀ {α : Type u} (x : m α), MonadAlgebra.lift x |>.monotone := by
  unfold Cont.monotone; intros; unfold MonadAlgebra.lift
  solve_by_elim [MonadAlgebraOrdered.bind_le]

instance (t : Type u) [MonadOrder m] [LawfulMonad m] [Preorder t] [MonadAlgebraOrdered m t] : LawfulMonadLift m (W t) where
  monadLift := fun x => ⟨MonadAlgebra.lift x, Cont.monotone_lift m x⟩
  monadMapPure := by intros; unfold MonadAlgebra.lift; simp [monadLift, pure, map_pure, MonadAlgebra.pure]
  monadMapBind := by intros; ext g; simp [monadLift, bind, MonadAlgebra.bind, MonadAlgebra.lift]; rfl
