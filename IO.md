# IO in Velvet

A Velvet program does IO by sending requests to *channels*. Its specs talk about the *trace*: every
request made and the answer it got. A program is proved against *protocols*, rules about what may
be asked and answered, and never against a particular implementation. It can then run against any
implementation that keeps to the protocols, including real `IO`, and the proof carries over.

This is a walk through the typeclasses, in the order you meet them. The running example is
`readFile fs p`, which returns the contents of path `p`; we prove it never fails, returns exactly
what is on the disk, and never leaves a file open.

Code: `Velvet/Core/FreerMonad/IO/` for the core, `Velvet/Examples/IO/` for the examples.

## 1. `Channel`: what can be asked

```lean
class Channel (c : Type) (op : outParam (Type → Type)) (Ev Err : outParam Type) where
  log : ∀ {α : Type}, op α → Except Err α → Ev
```

The values of `c` are channels: a socket, a file, stdout. A request `op α` is answered with an `α`
or fails with an `Err`, and `log` records the request and its answer as an `Ev` in the channel's
history.

| Channel `c` | Requests `op α` | Answer type `α` |
|---|---|---|
| `Stdin` | `read` | `String` |
| `Socket` | `read`, `write (r : Response)` | `Request`, `Unit` |
| `Fs` | `check p`, `open p` | `Bool`, `File` |
| `File` | `read`, `close` | `String`, `Unit` |

Opening hands out a `File`, which is itself a channel:

```lean
inductive FsOp : Type → Type where
  | check (p : String) : FsOp Bool
  | open (p : String) : FsOp File

inductive FileOp : Type → Type where
  | read : FileOp String
  | close : FileOp Unit
```

A program makes a request with `call`, and the request's type gives the answer's type:

```lean
let ok ← call fs (.check p)    -- ok : Bool
let f  ← call fs (.open p)     -- f : File
let s  ← call f .read          -- s : String
call f .close
```

Most channels are only read and written. `StreamChannel c In Out Err` declares one in a line, with
requests `read : StreamOp In Out In` and `write (o : Out) : StreamOp In Out Unit`, and gives `read
ch` and `write ch o` with their specs.

## 2. `Protocol`: what may be asked and answered

```lean
structure Protocol (c : Type) (op : Type → Type) (Ev Err : Type) where
  allow   : ∀ {α : Type}, c → List Ev → op α → Prop
  onReply : ∀ {α : Type}, c → List Ev → op α → Except Err α → Prop
```

Both sides see the channel and its history so far.

- `allow` is the program's obligation, checked at every call.
- `onReply` is what the program may assume about the answer.

Because protocols see the history, they can track state: a file is not used after it is closed, a
server only answers the request it is waiting on and only with the right answer, stdin fails only
with `eof`. They can also refer to an abstract world, so that what is proved holds for every world:

```lean
class FsWorld where
  contents : String → Option String

def fsP [FsWorld] : Protocol Fs FsOp FsEv FsErr where
  allow _ _ _ := True
  onReply _ h o r := match o, r with
    | .check p, .ok b => (b = true ↔ FsWorld.contents p ≠ none)
    | .open p, .ok f => f.path = p ∧ f ∉ opened h ∧ FsWorld.contents p ≠ none
    | .check _, .error _ => False
    | .open p, .error e => e = .notFound ∧ FsWorld.contents p = none

def fileP [FsWorld] : Protocol File FileOp FileEv FsErr where
  allow _ h _ := closed h = false
  onReply f h o r := match o, r with
    | .read, .ok s => FsWorld.contents f.path = some s
    | .read, .error e => e = .eof ∧ (closed h = true ∨ FsWorld.contents f.path = none)
    | .close, .ok _ => True
    | .close, .error e => e = .eof ∧ closed h = true
```

The filesystem reports truthfully whether a path exists and hands out fresh files; an open file
reads back what is on the disk; a closed file may not be touched.

## 3. `Provide` and `Distinguish`: one trace for every channel

A program's trace has one event type `E`. `Provide E c` says channel kind `c`'s events fit in it:

```lean
class Provide (E c : Type) {op : outParam (Type → Type)} {Ev Err : outParam Type} [Channel c op Ev Err] where
  inj : c → Ev → E
  proj : E → Option (c × Ev)
  proj_inj : ∀ ch e, proj (inj ch e) = some (ch, e)
```

Instances for products and sums mean `E` is just a sum of `channel × event` pairs:

```lean
abbrev Ev := (Fs × FsEv) ⊕ (File × FileEv)
```

`h.traceOf ch` is the history of one channel, and `h.recordFor ch e` appends an event to it.
`Distinguish E c c'` says events of kind `c` are never taken for kind `c'`, which the sum instances
derive. It gives framing: reading a file leaves the filesystem's history unchanged.

## 4. What a call means

```lean
inductive IOEff (E Err : Type) (m : Type → Type) [Monad m] [ModelBase m] : Type → Type 1 where
  | call {c : Type} {op : Type → Type} {Ev α : Type} [Channel c op Ev Err] [DecidableEq c] [Provide E c]
      {P : Protocol c op Ev Err} [Model c P E m] (ch : c) (o : op α) : IOEff E Err m α
  | snapshot : IOEff E Err m (Ghost (Trace E))
  | lift {α : Type} (x : m α) : IOEff E Err m α

abbrev IOProgT (E Err : Type) (m : Type → Type) [Monad m] [ModelBase m] := FreerMonad (IOEff E Err m)
abbrev IOProg (E Err : Type) := IOProgT E Err Option
```

`m` is the base monad the program runs in (section 6). The `Model` in a call says how it is
answered; verification never looks at it.

The rule for a call, with `Q` the postcondition, `S` the IO error postcondition and `B` the base
monad's:

```
{ fun h => allow (h.traceOf ch) o
         ∧ (∀ v, onReply (h.traceOf ch) o (.ok v)    → Q v (h.recordFor ch (log o (.ok v))))
         ∧ (∀ e, onReply (h.traceOf ch) o (.error e) → S e (h.recordFor ch (log o (.error e))))
         ∧ stopPre B }
    call ch o
{ Q ; signals S, B }
```

The program must be allowed to ask, and must cope with every answer the protocol permits. `stopPre
B` says what happens if the call stops instead of answering: over `Option` a call never stops and
it is `True`; over `IO` it is "`B` accepts every `IO` error".

`snapshot` returns the current trace as a ghost value, for specs and loop invariants.

## 5. Writing and proving a program

The spec states the whole trace the program leaves:

```lean
method readFile [FsWorld] (fs : Fs) (p : String) returns (r : Option String) in IOProg Ev FsErr
  given (h₀ : Trace Ev)
  requires (h : Trace Ev) => h = h₀ ∧ ∀ f : File, h.traceOf f ≠ [] → f ∈ opened (h.traceOf fs)
  signals (e : FsErr) (h : Trace Ev) => False
  signals False
  ensures (h : Trace Ev) => r = FsWorld.contents p
  ensures (h : Trace Ev) => ∀ f : File, h.traceOf f ≠ [] → f ∈ opened (h.traceOf fs)
  ensures (h : Trace Ev) => r = none → h.events = h₀.events ++ [.inl (fs, .checked p (.ok false))]
  ensures (h : Trace Ev) => ∀ s, r = some s → ∃ f : File, f ∉ opened (h₀.traceOf fs) ∧
    h.events = h₀.events ++
      [.inl (fs, .checked p (.ok true)), .inl (fs, .opened p (.ok f)),
        .inr (f, .read (.ok s)), .inr (f, .closed (.ok ()))]
do
  let ok ← call fs (.check p)
  if ok then
    let f ← call fs (.open p)
    let s ← call f .read
    call f .close
    return some s
  else
    return none

prove_correct readFile by
  velvet_vcgen [readFile]
  all_goals grind (ematch := 10)
```

It never fails and always returns (the two `signals False`), and returns what is on the disk. The
trace it leaves is either just a check, or a check, an open of a fresh file, one read and a close. Forgetting the
`close` breaks the last `ensures`; reading after it breaks `allow`.

## 6. Models: running a program

To run a program, each channel kind needs a `Model`: how it answers, in the base monad `m`, kept to
the protocol.

```lean
class Model {op : outParam (Type → Type)} {Ev Err : outParam Type} (c : Type) [Channel c op Ev Err]
    (P : outParam (Protocol c op Ev Err)) (E : Type) [DecidableEq c] [Provide E c]
    (m : Type → Type) [Monad m] [ModelBase m] where
  call : ∀ {α : Type}, Trace E → c → op α → m (Except Err α)
  call_ok : ∀ {α : Type} t ch (o : op α), yields (call t ch o) (P.onReply ch (t.traceOf ch) o)
```

`yields x R` comes from the base monad, which decides what keeping to the protocol means there:

```lean
class ModelBase (m : Type → Type) [Monad m] where
  yields : ∀ {α : Type}, m α → (α → Prop) → Prop
  ...  -- closed under pure and bind
```

- Over `Option`, `x` must return a result in `R`. So a call always answers, and programs can be
  proved to finish (`signals False`).
- Over `StateT σ m`, it must also leave the state alone.
- Over `IO`, a result it returns must be in `R`, but it may also throw. So any call may stop, and
  specs must accept every `IO` error.

A model with no effects is a `PureModel`, with `call : … → Except Err α` and a proof that each
answer satisfies `onReply`. It is a `Model` in every base monad. The models for `readFile` answer
from a given `FsWorld`.

The interpreter keeps the trace as state on top of `m`. Each call asks the model and records its
answer:

```lean
abbrev IOModelT (E Err : Type) (m : Type → Type) := ExceptT Err (StateT (Trace E) m)
```

Soundness says that a spec proved from the protocols holds of the interpreted program, whatever the
models:

```lean
theorem IOModelT.refines … (hx : Triple x pre post epost) :
    Triple (x.interp (m := IOModelT E Err m)) pre post epost
```

A program takes its models as parameters, so its proof covers every model. For example, in
`Basic.lean` the run of `reply s` always returns, and either the trace is one read and one reply or
the socket failed with `eof` or `reset`.

## 7. Real `IO`

`IO` is a base monad like the others. Its WP ignores the world:

```lean
wp x post epost := ∀ w, match x w with
  | .ok a _    => post a
  | .error e _ => epost e
```

A model over `IO` is ordinary `IO` code. `Model.monitored` turns any implementation into a model,
with no proof, by checking each answer against the protocol and throwing on one it does not allow:

```lean
def Model.monitored [CanStop m] (P : Protocol c op Ev Err)
    [∀ α ch h (o : op α) r, Decidable (P.onReply ch h o r)]
    (impl : ∀ {α : Type}, Trace E → c → op α → m (Except Err α)) : Model c P E m

def honest : Model Socket reqResp SockEvent IO :=
  Model.monitored reqResp fun _ _ o => match o with
    | .read => pure (.ok ⟨7⟩)
    | .write r => do IO.println s!"replying to {r.id}"; pure (.ok ())
```

`Monitor.lean` proves `serveOne` over `IO`, with `signals (e : IO.Error) => True`, and derives for
every model and every state of the world: if the run returns a request, the trace is one read of
it and one reply. An `IO` error promises nothing; that covers a real failure, the monitor stopping
the run, and running forever. The same program runs with an honest model, a lying one (stopped),
or a pure test model.

What is trusted: compiled `IO` behaves like its definition, and implementations do what they
report. The monitor checks answers, not effects: a `write` that answers `ok` without writing goes
unnoticed.

Protocols over an abstract world, like `fsP`, cannot be checked at runtime, since there is no
`FsWorld` value to compare against. They suit proofs and pure models; a protocol meant for a real
disk states what a real disk guarantees.

## 8. Loops

`Servers/Calc.lean` answers calculations until the client sends `quit` or hangs up. Its protocol
lets the server read only when no calculation is waiting and never after `quit`, and write only the
right answer to the waiting one.

```lean
set_option velvet.semantics.termination "partial" in
method serve [CalcClients] (c : Calc) returns (r : Unit) in IOProg CalcEv IOErr
  given (h₀ : Trace CalcEv)
  requires (h : Trace CalcEv) => h = h₀ ∧ calcPending (h.traceOf c) = none ∧ quitted (h.traceOf c) = false
  signals (e : IOErr) (h : Trace CalcEv) =>
    e = .eof ∧ ∃ os : List Op, h.traceOf c = h₀.traceOf c ++ os.flatMap exchange ++ [.read (.error .eof)]
  signals True
  ensures (h : Trace CalcEv) =>
    ∃ os : List Op, h.traceOf c = h₀.traceOf c ++ os.flatMap exchange ++ [.read (.ok .quit)]
do
  let start ← snapshot
  let ghost served := ([] : List Op)
  while true
    invariant answered : (fun h : Trace CalcEv =>
      h.traceOf c = start.reveal.traceOf c ++ served.reveal.flatMap exchange ∧
        calcPending (h.traceOf c) = none ∧ quitted (h.traceOf c) = false)
  do
    let q ← read c
    match q with
    | .quit => break
    | .op o =>
      write c o.eval
      served *:= served ++ [o]
  return ()
```

The server may run forever, so correctness is partial (`signals True`), but `allow` is still
checked at every step of every run. `serveN` answers at most `n` calculations and is proved to
finish. Over `IO`, Lean takes a diverging loop to throw some error, so loop specs accept every `IO`
error.

## 9. IO over another monad

Actions of the base monad run inside an IO program through `lift` (also `MonadLift`). They leave
the trace alone, and their spec is the base monad's own:

```
{ fun h => wp x (fun a => Q a h) B }  lift x  { Q ; signals S, B }
```

`Lift.lean` counts the requests a handler serves in a `StateT Nat` underneath the IO, so its specs
take the counter as well as the trace:

```lean
method countedReply [Clients] (s : Socket) returns (q : Request) in IOProgT SockEvent IOErr (StateT Nat Option)
  given (h₀ : Trace SockEvent) (n₀ : Nat)
  requires (h : Trace SockEvent) (n : Nat) => h = h₀ ∧ n = n₀
  signals (e : IOErr) (h : Trace SockEvent) (n : Nat) => True
  signals False
  ensures (h : Trace SockEvent) (n : Nat) =>
    n = n₀ + 1 ∧ h.events = h₀.events ++ [(s, .read (.ok q)), (s, .write ⟨q.id⟩ (.ok ()))]
do
  let q ← read s
  modify (· + 1)
  write s (Response.mk q.id)
  return q
```
