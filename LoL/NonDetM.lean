import Mathlib.Data.Set.Basic

universe u v


inductive NonDetM (α : Type u) where
  | none : NonDetM α
  | more : α → (Unit → NonDetM α) → NonDetM α

variable {α : Type u} {β : Type v}

def NonDetM.union : NonDetM α → NonDetM α → NonDetM α
  | NonDetM.none, ys => ys
  | NonDetM.more x xs, ys => NonDetM.more x (fun () => union (xs ()) ys)

def NonDetM.choose : List α → NonDetM α
  | [] => NonDetM.none
  | x :: xs => NonDetM.more x (fun () => NonDetM.choose xs)

def NonDetM.take : Nat → NonDetM α → List α
  | 0, _ => []
  | _ + 1, NonDetM.none => []
  | n + 1, NonDetM.more x xs => x :: (xs ()).take n

def NonDetM.takeAll : NonDetM α → List α
  | NonDetM.none => []
  | NonDetM.more x xs => x :: (xs ()).takeAll

abbrev NonDetM.one (x : α) : NonDetM α := NonDetM.more x (fun () => NonDetM.none)

abbrev NonDetM.bind : NonDetM α → (α → NonDetM β) → NonDetM β
  | NonDetM.none, _ =>
    NonDetM.none
  | NonDetM.more x xs, f => f x |>.union <| xs () |>.bind f


instance : Monad NonDetM where
  pure := .one
  bind := .bind

lemma NonDetM.takeAll_union (x y : NonDetM α) : (x.union y).takeAll = x.takeAll ++ y.takeAll := by
  induction x generalizing y
  rfl; simp [NonDetM.union, NonDetM.takeAll, *] at *

instance : LawfulMonad NonDetM where
  map_const      := by intros; rfl
  id_map         := by
    intros _ x; induction x
    rfl; simp [Functor.map, NonDetM.bind, NonDetM.union, *] at *
    rename_i h; simp [h ()]
  comp_map       := by
    intros _ _ _ f g x; induction x
    rfl; simp [Functor.map, NonDetM.bind, NonDetM.union, *] at *
    rename_i h; simp [h ()]
  seqLeft_eq     := by
    intros _ _ x y;  induction x
    rfl; simp [Functor.map, NonDetM.bind, NonDetM.union, *, SeqLeft.seqLeft] at *
    rename_i h; simp [h ()]; rfl
  seqRight_eq    := by
    intros _ _ x y;  induction x
    rfl; simp [Functor.map, NonDetM.bind, NonDetM.union, *, SeqRight.seqRight, Seq.seq] at *
    rename_i h; simp [h ()]; cases y <;> try simp
    simp [NonDetM.union]; sorry
  map_pure       := by intros; rfl
  seq_pure       := by intros; rfl
  seq_assoc      := by intros; sorry
  bind_pure_comp := by intros; rfl
  bind_map       := by intros; rfl
  bind_assoc     := by intros; sorry
  pure_bind      := by intros; sorry
  pure_seq       := by intros; sorry

class MonadFinNonDet (m : Type u → Type v) where
  /-- `(← read) : ρ` reads the state out of monad `m`. -/
  choose : List α → m α

export MonadFinNonDet (choose)

universe w

instance {α} {m : Type u → Type v} {n : Type u → Type w} [MonadLift m n] [@MonadFinNonDet α m] : @MonadFinNonDet α n where
  choose l := liftM (m := m) <| choose l

instance : @MonadFinNonDet α NonDetM where
  choose := NonDetM.choose
