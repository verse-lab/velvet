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
Constructors:
- `pure`: standard monadic pure
- `vis`: embedding effects from base monad `m`
- `pickCont`: non-deterministic choice satisfying predicate `p` with continuation `f` and optional runtime finder `find`
- `repeatCont`: loop iteration with state `init`, body `f`, and post-loop continuation `cont`
-/
public inductive NonDetT (mode : NondetMode) (m : Type u → Type v) : (α : Type u) → Type (max (u + 1) v) where
  | pure {α : Type u} (ret : α) : NonDetT mode m α
  | vis {α : Type u} {β : Type u} (x : m β) (f : β → NonDetT mode m α) : NonDetT mode m α
  | pickCont {α : Type u} (τ : Type u) (p : τ → Prop) (find : Unit → Option τ) (f : τ → NonDetT mode m α) : NonDetT mode m α
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
  | pickCont τ p find f' => pickCont τ p find fun t => bind (f' t) f
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
  | pickCont τ p find f ih =>
    show pickCont τ p find (fun t => f t >>= pure) = pickCont τ p find f
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
  | pickCont τ p find f' ih =>
    show pickCont τ p find (fun t => (f' t >>= f) >>= g) = pickCont τ p find (fun t => f' t >>= fun z => f z >>= g)
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
  NonDetT.pickCont τ (fun _ => True) (fun _ => some default) pure

/-- Assume a decidable proposition `as`. -/
public protected def «assume» {mode : NondetMode} {m : Type u → Type v} (as : Prop) [Decidable as] : NonDetT mode m PUnit.{u+1} :=
  NonDetT.pickCont PUnit.{u+1} (fun _ => as) (fun _ => if as then some PUnit.unit else none) (fun _ => pure .unit)

/-- Pick a value of type `τ` satisfying property `p`. -/
public protected def pickSuchThat {mode : NondetMode} {m : Type u → Type v} (τ : Type u) (p : τ → Prop)
    [hint : FindHint p] (_name : Lean.Name := .anonymous) : NonDetT mode m τ :=
  NonDetT.pickCont τ p hint.find pure

/-- Repeat a loop step until completion. -/
public def «repeat» {mode : NondetMode} {m : Type u → Type v} {α : Type u}
    (init : α) (f : α → NonDetT mode m (ForInStep α)) : NonDetT mode m α :=
  NonDetT.repeatCont init f pure

end NonDetT

/-- Non-determinism effect class. -/
public class MonadNonDet (m : Type u → Type v) where
  pick : (τ : Type u) → [Inhabited τ] → m τ
  pickSuchThat : (τ : Type u) → (p : τ → Prop) → [_hint : FindHint p] → (name : Lean.Name := .anonymous) → m τ
  assume : (as : Prop) → [Decidable as] → m PUnit.{u+1}
  rep {α : Type u} : α → (α → m (ForInStep α)) → m α

export MonadNonDet (pick pickSuchThat assume rep)

public instance {mode : NondetMode} {m : Type u → Type v} : MonadNonDet (NonDetT mode m) where
  pick := NonDetT.pick
  assume := NonDetT.«assume»
  pickSuchThat τ p [FindHint p] (name := .anonymous) := NonDetT.pickSuchThat τ p name
  rep := NonDetT.repeat

/-- Loop iteration instance for `NonDetT mode m`, routing loops to `repeatCont`. -/
public instance instForInLoopNonDetT {mode : NondetMode} {m : Type u → Type v} :
    ForIn (NonDetT mode m) Lean.Loop Unit where
  forIn _ init f := NonDetT.repeatCont init (f ()) pure

/-- Extract a meaningful identifier name from a choice binder syntax,
falling back to `"choice"` if no identifier is found. -/
public meta partial def extractChoiceName (stx : Lean.Syntax) : Lean.Name :=
  match stx with
  | Lean.Syntax.ident _ _ val _ => val.eraseMacroScopes
  | Lean.Syntax.node _ ``Lean.Parser.Term.typeAscription args =>
      if h : 1 < args.size then
        match args[1] with
        | Lean.Syntax.ident _ _ val _ => val.eraseMacroScopes
        | other => extractChoiceName other
      else `choice
  | Lean.Syntax.node _ ``Lean.Parser.Term.paren args =>
      if h : 1 < args.size then
        match args[1] with
        | Lean.Syntax.ident _ _ val _ => val.eraseMacroScopes
        | other => extractChoiceName other
      else `choice
  | _ => `choice

/-- Hilbert choice operator notation: `let x :| p` inside `do` blocks,
optionally with an explicit name label: `let name : x :| p`. -/
syntax "let" (atomic(ident " : "))? term ":|" term : doElem

macro_rules
  | `(doElem| let $[$nm:ident :]? $x:term :| $t) => do
    let name := match nm with
      | some n => n.getId
      | none => extractChoiceName x.raw
    let nameStr := Lean.Syntax.mkStrLit name.toString
    let nameTerm : Lean.TSyntax `term ← `(Lean.Name.mkSimple $nameStr)
    `(doElem| let $x:term ← MonadNonDet.pickSuchThat _ (fun $x => $t) $nameTerm)

end
