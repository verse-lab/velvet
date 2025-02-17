import LoL.Functors
import LoL.MonadAlgebras.EffectObservations

universe u v w

class TransformerAlgebra (t : (Type u -> Type u) -> (Type u -> Type v)) (m : outParam (Type u -> Type u))
  [Monad m] [inst: MonadTransformer t] where
  hasmorphism {x : Type u} [MonadAlgebra m x] :
    @MonadAlgebra (t m) inst.isMonad (m x)
