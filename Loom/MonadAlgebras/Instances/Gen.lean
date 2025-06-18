import Loom.MonadAlgebras.Defs
import Loom.MonadAlgebras.Instances.Basic
import Loom.MonadAlgebras.Instances.ReaderT
import Loom.MonadAlgebras.Instances.StateT
import Plausible.Gen

open Plausible

universe u

instance MPropGenInst : MPropOrdered Gen (ULift Nat -> ULift StdGen -> Prop) :=
  inferInstanceAs
    (MPropOrdered
      (ReaderT (ULift Nat)
        (StateT (ULift StdGen) Id))
      (ULift Nat ->
        ULift StdGen -> Prop))
