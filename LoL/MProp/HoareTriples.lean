import LoL.MProp.EffectObservations
import LoL.MProp.Instances

universe u v w

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u}
variable {l : Type u} [Preorder l]
variable [MProp m l]

def triple (pre : m PProp) (c : m α) (post : α -> m PProp) : Prop :=
  MProp.μ pre ≤ liftM (n := Cont l) c (MProp.μ (m := m) ∘ post)
