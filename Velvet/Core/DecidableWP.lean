module

public import Std.WP

@[expose] public section

namespace Velvet.Testing

/-- The result of checking one supplied input against a method contract. -/
inductive TestVerdict where
  | pass
  | fail
  | discard
  deriving Repr, BEq, DecidableEq

/-- Executable, pointwise decisions for assertions and exception assertion stacks.
Function arguments are supplied by the caller, not universally searched. -/
class AssertionDecidability (Pred : Type u) where
  PointwiseDecidable : Pred → Type u

abbrev PointwiseDecidable {Pred : Type u} [AssertionDecidability Pred] (p : Pred) :=
  AssertionDecidability.PointwiseDecidable p

instance : AssertionDecidability Prop where
  PointwiseDecidable p := Decidable p

instance {α : Type u} {Pred : Type v} [AssertionDecidability Pred] :
    AssertionDecidability (α → Pred) where
  PointwiseDecidable p := ∀ a, PointwiseDecidable (p a)

instance [AssertionDecidability P] [AssertionDecidability Q] : AssertionDecidability (P × Q) where
  PointwiseDecidable p := PointwiseDecidable p.1 × PointwiseDecidable p.2

instance : AssertionDecidability Unit where
  PointwiseDecidable _ := Unit

open Std.WP Lean.Order

/-- An executable decision procedure for a selected WP interpretation. Each leaf decision
carries a proof, connecting the tester to that interpretation. Custom monads can supply an
instance; the WP laws alone are deliberately insufficient to derive a tester. -/
class DecidableWP (m : Type u → Type v) (Pred : outParam (Type w))
    (EPred : outParam (Type z)) [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [AssertionDecidability Pred] [AssertionDecidability EPred] where
  decideWP {α : Type u} (x : m α) (post : α → Pred) (epost : EPred)
    (postDec : ∀ a, PointwiseDecidable (post a)) (epostDec : PointwiseDecidable epost) :
    PointwiseDecidable (wp x post epost)

abbrev decideWP {m : Type u → Type v} [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [AssertionDecidability Pred] [AssertionDecidability EPred]
    [DecidableWP m Pred EPred] {α : Type u} (x : m α) (post : α → Pred) (epost : EPred)
    (postDec : ∀ a, PointwiseDecidable (post a)) (epostDec : PointwiseDecidable epost) :=
  DecidableWP.decideWP x post epost postDec epostDec

instance : DecidableWP Id Prop Unit where
  decideWP x _ _ postDec _ := postDec x

instance : DecidableWP Option Prop (Unit → Prop) where
  decideWP x _ _ postDec epostDec :=
    match x with
    | some a => postDec a
    | none => epostDec ()

instance : DecidableWP (Except ε) Prop (ε → Prop) where
  decideWP x _ _ postDec epostDec :=
    match x with
    | .ok a => postDec a
    | .error e => epostDec e

instance {m : Type u → Type v} {S : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [AssertionDecidability Pred] [AssertionDecidability EPred] [DecidableWP m Pred EPred] :
    DecidableWP (StateT S m) (S → Pred) EPred where
  decideWP x post epost postDec epostDec := fun s =>
    decideWP (x.run s) (fun (a, s') => post a s') epost
      (fun (a, s') => postDec a s') epostDec

instance {m : Type u → Type v} {R : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [AssertionDecidability Pred] [AssertionDecidability EPred] [DecidableWP m Pred EPred] :
    DecidableWP (ReaderT R m) (R → Pred) EPred where
  decideWP x post epost postDec epostDec := fun r =>
    decideWP (x.run r) (fun a => post a r) epost (fun a => postDec a r) epostDec

instance {m : Type u → Type v} {ε : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [AssertionDecidability Pred] [AssertionDecidability EPred] [DecidableWP m Pred EPred] :
    DecidableWP (ExceptT ε m) Pred ((ε → Pred) × EPred) where
  decideWP x post epost postDec epostDec :=
    decideWP x.run (pushExcept post epost.1) epost.2
      (fun r => match r with
        | .ok a => postDec a
        | .error e => epostDec.1 e) epostDec.2

instance {m : Type u → Type v} {Pred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [AssertionDecidability Pred] [AssertionDecidability EPred] [DecidableWP m Pred EPred] :
    DecidableWP (OptionT m) Pred ((Unit → Pred) × EPred) where
  decideWP x post epost postDec epostDec :=
    decideWP x.run (pushOption post epost.1) epost.2
      (fun r => match r with
        | some a => postDec a
        | none => epostDec.1 ()) epostDec.2

instance : DecidableWP (EStateM ε S) (S → Prop) (ε → S → Prop) where
  decideWP x post epost postDec epostDec := fun s =>
    show Decidable (match x s with
      | .ok a s' => post a s'
      | .error e s' => epost e s') from
    match x s with
    | .ok a s' => postDec a s'
    | .error e s' => epostDec e s'

/-- Keep execution behind a thunk so rejected inputs never run the program. -/
def check (pre : Prop) (preDec : Decidable pre) (run : Unit → Bool) : TestVerdict :=
  match preDec with
  | .isFalse _ => .discard
  | .isTrue _ => if run () then .pass else .fail

end Velvet.Testing
