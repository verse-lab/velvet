import Velvet.Core.FreerMonad.IO.Trace
import Velvet.Core.FreerMonad.IO.ModelBase

/-- How a channel kind answers in the base monad `m`, as a function of the trace so far: only with
replies the protocol allows. Interpreting a program needs one for every channel it uses; verifying it
does not look at it. -/
class Model {op : outParam (Type → Type)} {Ev Err : outParam Type} (c : Type) [Channel c op Ev Err]
    (P : outParam (Protocol c op Ev Err)) (E : Type) [DecidableEq c] [Provide E c]
    (m : Type → Type) [Monad m] [ModelBase m] where
  call : ∀ {α : Type}, Trace E → c → op α → m (Except Err α)
  call_ok : ∀ {α : Type} t ch (o : op α), yields (call t ch o) (P.onReply ch (t.traceOf ch) o)

/-- A model without effects, which answers in every base monad. -/
class PureModel {op : outParam (Type → Type)} {Ev Err : outParam Type} (c : Type) [Channel c op Ev Err]
    (P : outParam (Protocol c op Ev Err)) (E : Type) [DecidableEq c] [Provide E c] where
  call : ∀ {α : Type}, Trace E → c → op α → Except Err α
  call_ok : ∀ {α : Type} t ch (o : op α), P.onReply ch (t.traceOf ch) o (call t ch o)

section
variable {c E Ev Err : Type} {op : Type → Type} [Channel c op Ev Err] [DecidableEq c] [Provide E c]
  {m : Type → Type} [Monad m] [ModelBase m]

instance instModelOfPure {P : Protocol c op Ev Err} [PureModel c P E] : Model c P E m where
  call t ch o := pure (PureModel.call (P := P) t ch o)
  call_ok t ch o := ModelBase.yields_pure (PureModel.call_ok t ch o)

/-- Any implementation, its replies checked against `P`: one `P` does not allow stops the run. -/
@[instance_reducible] def Model.monitored [CanStop m] (P : Protocol c op Ev Err)
    [∀ (α : Type) (ch : c) (h : List Ev) (o : op α) (r : Except Err α), Decidable (P.onReply ch h o r)]
    (impl : ∀ {α : Type}, Trace E → c → op α → m (Except Err α))
    (free : ∀ {α : Type} t ch (o : op α), yields (impl t ch o) fun _ => True := by intros; simp) :
    Model c P E m where
  call t ch o := ModelBase.monitor (P.onReply ch (t.traceOf ch) o) (impl t ch o)
  call_ok t ch o := ModelBase.yields_monitor _ _ (free t ch o)

end

/-- The monad IO programs over `m` are interpreted into: the trace is the state, a reply may be an
error, and everything else is `m`. -/
abbrev IOModelT (E Err : Type) (m : Type → Type) := ExceptT Err (StateT (Trace E) m)

/-- `IOModelT` over `Option`, where `none` is divergence. -/
abbrev IOModel (E Err : Type) := IOModelT E Err Option
