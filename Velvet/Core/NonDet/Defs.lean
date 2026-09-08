module

public import Velvet.Core.NonDet.Findable
public import Velvet.Core.Named

universe u v

@[expose] public section

/-- Choice mode for non-determinism:
- `demonic`: adversarial / universal choice (Dijkstra / Hoare verification: must succeed for all choices)
- `angelic`: cooperative / existential choice (Synthesis / Relational execution: succeeds if at least one choice succeeds)
-/
public inductive NondetMode where
  | demonic
  | angelic
  deriving DecidableEq, Repr, Inhabited

export NondetMode (demonic angelic)


/-- Non-determinism monad transformer parameterized by `NondetMode`.

NOTE: `NonDetT` is designed using an Interaction Tree (ITree) / Freer monad approach,
acting as an AST that sits at the **top of the monad stack** (e.g. `DemonicT (StateT σ Option)`
or `DemonicT Option`). Having `NonDetT` at the top allows:
1. Constructive execution via handler/interpreter evaluation (`NonDetT.run`).
2. Syntax-directed weakest-precondition generation (`NonDetT.wp`).
Base effects from the underlying monad `m` are freely embedded into tree leaves via `.vis`
(`MonadLift m (NonDetT mode m)`), following the Freer monad pattern.

Constructors:
- `pure`: standard monadic pure
- `vis`: embedding effects from base monad `m` (Freer effect node)
- `pickCont`: non-deterministic choice satisfying predicate `p` with continuation `f`, backed by complete `Findable p`
- `repeatCont`: loop iteration with state `init`, body `f`, and post-loop continuation `cont`
-/
public inductive NonDetT (mode : NondetMode) (m : Type u → Type v) : (α : Type u) → Type (max (u + 1) v) where
  | pure {α : Type u} (ret : α) : NonDetT mode m α
  | vis {α : Type u} {β : Type u} (x : m β) (f : β → NonDetT mode m α) : NonDetT mode m α
  | pickCont {α : Type u} (τ : Type u) (p : τ → Prop) [wf : Findable p] (f : τ → NonDetT mode m α) : NonDetT mode m α
  | repeatCont {α : Type u} {β : Type u} (init : β) (f : β → NonDetT mode m (ForInStep β)) (cont : β → NonDetT mode m α) : NonDetT mode m α

/-- Shorthand alias for demonic non-determinism. -/
public abbrev DemonicT (m : Type u → Type v) := NonDetT .demonic m

/-- Shorthand alias for angelic non-determinism. -/
public abbrev AngelicT (m : Type u → Type v) := NonDetT .angelic m

namespace NonDetT

public def bind {mode : NondetMode} {m : Type u → Type v} {α β : Type u}
    (x : NonDetT mode m α) (f : α → NonDetT mode m β) : NonDetT mode m β :=
  match x with
  | pure ret => f ret
  | vis x f' => vis x fun y => bind (f' y) f
  | pickCont τ p f' => pickCont τ p fun t => bind (f' t) f
  | repeatCont init f' cont => repeatCont init f' fun t => bind (cont t) f

public instance {mode : NondetMode} {m : Type u → Type v} : Monad (NonDetT mode m) where
  pure := NonDetT.pure
  bind := NonDetT.bind

public instance {mode : NondetMode} {m : Type u → Type v} : MonadLift m (NonDetT mode m) where
  monadLift x := NonDetT.vis x NonDetT.pure

theorem bind_pure {mode : NondetMode} {m : Type u → Type v} {α : Type u} (x : NonDetT mode m α) :
    (x >>= pure) = x := by
  induction x with
  | pure ret => rfl
  | vis x f ih =>
    show vis x (fun y => f y >>= pure) = vis x f
    congr 1; funext y; exact ih y
  | pickCont τ p f ih =>
    show pickCont τ p (fun t => f t >>= pure) = pickCont τ p f
    congr 1; funext t; exact ih t
  | repeatCont init f' cont _ ih =>
    show repeatCont init f' (fun t => cont t >>= pure) = repeatCont init f' cont
    congr 1; funext t; exact ih t

theorem id_map' {mode : NondetMode} {m : Type u → Type v} {α : Type u} (x : NonDetT mode m α) :
    (id <$> x) = x := by
  change (x >>= fun a => pure (id a)) = x
  simp only [id]
  exact NonDetT.bind_pure x

theorem pure_bind' {mode : NondetMode} {m : Type u → Type v} {α β : Type u} (x : α) (f : α → NonDetT mode m β) :
    (pure x >>= f) = f x := rfl

theorem bind_assoc' {mode : NondetMode} {m : Type u → Type v} {α β γ : Type u}
    (x : NonDetT mode m α) (f : α → NonDetT mode m β) (g : β → NonDetT mode m γ) :
    ((x >>= f) >>= g) = (x >>= fun y => f y >>= g) := by
  induction x with
  | pure ret => rfl
  | vis x f' ih =>
    show vis x (fun y => (f' y >>= f) >>= g) = vis x (fun y => f' y >>= fun z => f z >>= g)
    congr 1; funext y; exact ih y f
  | pickCont τ p f' ih =>
    show pickCont τ p (fun t => (f' t >>= f) >>= g) = pickCont τ p (fun t => f' t >>= fun z => f z >>= g)
    congr 1; funext t; exact ih t f
  | repeatCont init f' cont _ ih =>
    show repeatCont init f' (fun t => (cont t >>= f) >>= g) = repeatCont init f' (fun t => cont t >>= fun z => f z >>= g)
    congr 1; funext t; exact ih t f

public instance {mode : NondetMode} {m : Type u → Type v} : LawfulMonad (NonDetT mode m) :=
  LawfulMonad.mk' (NonDetT mode m)
    NonDetT.id_map'
    NonDetT.pure_bind'
    NonDetT.bind_assoc'

/-- Pick an arbitrary value of type `τ`. -/
public protected def pick {mode : NondetMode} {m : Type u → Type v} (τ : Type u) [Inhabited τ] : NonDetT mode m τ :=
  NonDetT.pickCont τ (fun _ => True) pure

/-- Assume a proposition `as`.
If a `Decidable as` instance is available in scope, it is used for runtime
interpretation; otherwise it fails at runtime with `none`. -/
public def assume' {mode : NondetMode} {m : Type u → Type v} (as : Prop) [Decidable as] : NonDetT mode m PUnit.{u+1} :=
  NonDetT.pickCont PUnit.{u+1} (fun _ => as) (fun _ => pure .unit)

/-- Pick a value of type `τ` satisfying property `p`, equipped with a complete `Findable` generator. -/
public def pickSuchThat {mode : NondetMode} {m : Type u → Type v} (τ : Type u) (p : τ → Prop)
    [wf : Findable p] (_name : Lean.Name := .anonymous) : NonDetT mode m τ :=
  NonDetT.pickCont τ p pure

/-- Repeat a loop step until completion. -/
public def repeat' {mode : NondetMode} {m : Type u → Type v} {α : Type u}
    (init : α) (f : α → NonDetT mode m (ForInStep α)) : NonDetT mode m α :=
  NonDetT.repeatCont init f pure

end NonDetT

export NonDetT (pick pickSuchThat assume' repeat')

/-- Loop iteration instance for `NonDetT mode m`, routing loops to `repeatCont`. -/
public instance instForInLoopNonDetT {mode : NondetMode} {m : Type u → Type v} :
    ForIn (NonDetT mode m) Lean.Loop Unit where
  forIn _ init f := NonDetT.repeatCont init (f ()) pure

end
