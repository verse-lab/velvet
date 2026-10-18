import Velvet.Core.Named
import Velvet.Core.Loop.Gadgets
import Std.WP

open Lean.Order

universe u v

inductive FreerMonad (e : Type u -> Type v) : (α : Type w) -> Type _ where
  | ret {α} (x : α) : FreerMonad e α
  | vis {β α} (x : e β) (k : β -> FreerMonad e α) : FreerMonad e α
  | iter {α} {β} (init : β) (body : β → FreerMonad e (ForInStep β)) (k : β -> FreerMonad e α) : FreerMonad e α

def FreerMonad.bind {e : Type u -> Type v} (x : FreerMonad e α) (f : α -> FreerMonad e β) : FreerMonad e β :=
  match x with
  | FreerMonad.ret x => f x
  | FreerMonad.vis x k => FreerMonad.vis x (fun x => (k x).bind f)
  | FreerMonad.iter body init k => FreerMonad.iter body init (fun x => (k x).bind f)

instance {e : Type u -> Type v} : Monad (FreerMonad e) where
  pure := FreerMonad.ret
  bind := FreerMonad.bind

variable [Monad m]

variable [CompleteLattice l]

class HasInterpreter (e : Type u -> Type v) (m : outParam (Type u -> Type w)) where
  interp : e α -> m α

export HasInterpreter (interp)

/-- The free monad laws are structural: they need neither an interpreter nor any law of `m`. -/
instance {e : Type u -> Type v} : LawfulMonad (FreerMonad e) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { intro _ x; induction x
    <;> simp [Functor.map, FreerMonad.bind]
    <;> solve_by_elim [funext] }
  { intro _ _ x; simp [bind, FreerMonad.bind, pure] }
  intro _ _ _ x f g; induction x
  <;> simp [bind, FreerMonad.bind]
  <;> solve_by_elim [funext]

def FreerMonad.interp [∀ γ, CCPO (m γ)] [MonoBind m]
  [HasInterpreter e m] : FreerMonad e α -> m α
  | FreerMonad.ret x => pure x
  | FreerMonad.vis x k => HasInterpreter.interp x >>= fun x => (k x).interp
  | FreerMonad.iter init body k =>
    Loop.forIn.loop (fun _ x => (body x).interp) init >>= (fun x => (k x).interp)


@[simp]
theorem FreerMonad.interp_bind
  [LawfulMonad m]
  [∀ α, Lean.Order.CCPO (m α)]
  [Lean.Order.MonoBind m]
  [HasInterpreter e m] : ∀ (x : FreerMonad e α) (y : α -> FreerMonad e β), (x.bind y).interp = x.interp >>= fun x => (y x).interp := by
  intro x; unhygienic induction x <;> simp [FreerMonad.bind, interp]
  { simp [k_ih] }
  simp [k_ih]
