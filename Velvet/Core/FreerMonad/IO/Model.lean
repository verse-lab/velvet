import Velvet.Core.FreerMonad.IO.Trace

/-- How a channel kind answers, as a function of the trace so far. Interpreting a program needs one
for every channel it uses; verifying it does not look at it. -/
class Model {op : outParam (Type → Type)} {Ev Err : outParam Type} (c : Type) [Channel c op Ev Err]
    (P : outParam (Protocol c op Ev Err)) (E : Type) [DecidableEq c] [Provide E c] where
  call : ∀ {α : Type}, Trace E → c → op α → Except Err α
  call_ok : ∀ {α : Type} t ch (o : op α), P.onReply ch (t.traceOf ch) o (call t ch o)

/-- The monad IO programs are interpreted into: the trace is the state, a reply may be an error, and
`none` is divergence. -/
abbrev IOModel (E Err : Type) := ExceptT Err (StateT (Trace E) Option)
