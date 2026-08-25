module

public import Velvet
public meta import Velvet

open Std.WP

namespace Velvet.Examples.StateT

public abbrev CounterOption := StateT Nat Option
public abbrev CounterExceptOption := StateT Nat (ExceptT String Option)

#check instMonadLiftT

/- A `StateT Nat Option` loop exercising invariant, decreasing, and done gadgets. -/
method countState (n : Nat) returns (res: Nat) in CounterOption
    requires (s : Nat) => True
    signals (_ : Unit) => False
    ensures (s : Nat) => res = n ∧ s = n
  do
  set 0
  let mut i := 0
  while' i < n
    invariant state_tracks : (fun s : Nat => s = i ∧ i ≤ n)
    decreasing by_remaining : n - i
    done_with state_done : (fun s : Nat => i = n ∧ s = n)
  do
    i := i + 1
    set i
  return i

prove_correct countState by
  velvet_vcgen [countState] with finish

#check countState.spec


/-- A `StateT Nat Option` program with assertions before and after mutation. -/
@[expose] public def boundedIncrement (limit : Nat) : CounterOption Nat := do
  let current ← get
  assert within_limit : (fun _ : Nat => current < limit)
  set (current + 1)
  assert state_advanced : (fun s : Nat => s = current + 1)
  return current

public theorem boundedIncrement_correct (limit : Nat) :
    Triple (boundedIncrement limit)
      (fun s => s < limit)
      (fun current s => current < limit ∧ s = current + 1)
      (fun (_ : Unit) => False) := by
  velvet_vcgen [boundedIncrement] with finish

/-- A finite-range loop over `StateT Nat Option`. -/
@[expose] public def countRange (n : Nat) : CounterOption Nat := do
  set 0
  let mut count := 0
  for' i in List.range n
    invariant count_tracks : (fun s : Nat => s = i ∧ count = i)
    done_with count_done : (fun s : Nat => s = n ∧ count = n)
  do
    count := i + 1
    set count
  return count

public theorem countRange_correct (n : Nat) :
    Triple (countRange n)
      (fun _ => True)
      (fun r s => r = n ∧ s = n)
      (fun (_ : Unit) => False) := by
  velvet_vcgen [countRange] with finish




/- A larger `StateT Nat (ExceptT String Option)` stack. -/
method checkedAdd (delta : Nat) returns (res: Nat) in CounterExceptOption
    requires (s : Nat) => True
    signals err_msg : (error : String) => error = "delta must be positive"
    signals (_ : Unit) => False
    ensures (s : Nat) => s = res + delta do
  let current ← get
  if delta = 0 then
    throw "delta must be positive"
  assert positive_delta : (fun _ : Nat => 0 < delta)
  set (current + delta)
  assert state_increased : (fun s : Nat => s = current + delta)
  return current

prove_correct checkedAdd by
  velvet_vcgen [checkedAdd] with finish
  /- all_goals omega -/
  


/- A stateful loop that either reaches `target` or throws at `blocked`. -/
method countUnlessBlocked (target: Nat) (blocked: Nat) returns (res: Nat) in CounterExceptOption
  requires (s : Nat) => True
  signals (e : String) => e = "blocked"
  signals (_ : Unit) => False
  ensures (s : Nat) => res = target ∧ s = target
do
  set 0
  let mut i := 0
  while' i < target
    invariant progress : (fun s : Nat => s = i ∧ i ≤ target)
    decreasing remaining : target - i
    done_with reached_target : (fun s : Nat => i = target ∧ s = target)
  do
    if i = blocked then
      throw "blocked"
    i := i + 1
    set i
  return i


/-
On success the loop reaches `target`. Since `StateT` is outside `ExceptT`, an
exception has no resulting state, so its postcondition observes only the error.
-/
prove_correct countUnlessBlocked by
  velvet_vcgen [countUnlessBlocked] with finish



/-- `StateT` outside `ReaderT`; assertions have shape `Nat → Nat → Prop`. -/
public abbrev ReaderCounter := StateT Nat (ReaderT Nat Id)

/-- Count from the initial state up to the reader-provided limit. -/
@[expose] public def countToReaderLimit : ReaderCounter Nat := do
  let limit ← readThe Nat
  let start ← get
  assert initial_bound :
    (fun state environment => state = start ∧ start ≤ environment ∧ environment = limit)
  let mut i := start
  while' i < limit
    invariant reader_progress :
      (fun state environment => environment = limit ∧ state = i ∧ i ≤ limit)
    decreasing reader_remaining : limit - i
    done_with reader_done :
      (fun state environment => environment = limit ∧ i = limit ∧ state = limit)
  do
    i := i + 1
    set i
  return i

/-- The precondition ensures that counting up to the configured limit is possible. -/
public theorem countToReaderLimit_correct :
    Triple countToReaderLimit
      (fun state limit => state ≤ limit)
      (fun result state limit => result = limit ∧ state = limit)
      PUnit.unit := by
  velvet_vcgen [countToReaderLimit] with finish

/- A method without `signals` in a monad stack with 0 exception channels (`ReaderCounter`). -/
method countToReaderLimitMethod returns (res : Nat) in ReaderCounter
    requires (s : Nat) (env : Nat) => True
    ensures (s : Nat) (env : Nat) => res = s do
  let start ← get
  return start

#print countToReaderLimitMethod.spec_triple
prove_correct countToReaderLimitMethod by
  velvet_vcgen [countToReaderLimitMethod] with finish

/-- The triangular number `0 + 1 + ... + n`. -/
@[expose] public def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)

/-- Add `1 + ... + limit` from the reader environment to the initial state. -/
@[expose] public def addToReaderLimit : ReaderCounter Nat := do
  let limit ← readThe Nat
  let initial ← get
  assert initial_snapshot :
    (fun state environment => state = initial ∧ environment = limit)
  let mut i := 0
  while' i < limit
    invariant accumulated_sum :
      (fun state environment =>
        environment = limit ∧ state = initial + triangular i ∧ i ≤ limit)
    decreasing additions_remaining : limit - i
    done_with all_added :
      (fun state environment =>
        environment = limit ∧ i = limit ∧ state = initial + triangular limit)
  do
    let current ← get
    set (current + (i + 1))
    i := i + 1
  return initial

/--
`triangular limit` is mathematically `limit * (limit + 1) / 2`. The result
remembers the initial state, and the final state contains the accumulated sum.
-/
public theorem addToReaderLimit_correct :
    Triple addToReaderLimit
      (fun initial limit => initial ≤ limit)
      (fun initial final limit =>
        initial ≤ limit ∧ final = initial + triangular limit)
      PUnit.unit := by
  velvet_vcgen [addToReaderLimit] with try finish
  all_goals (dsimp [triangular]; omega)

/- A zero-binder monad stack (`Id`): `requires`/`ensures` are plain `Prop`s with no binders. -/
method idNoBinders returns (res : Nat) in Id
  requires True
  ensures res = 1
do
  return 1

#check idNoBinders
prove_correct idNoBinders by
  velvet_vcgen [idNoBinders] with finish

#print idNoBinders.spec_triple

/- Total correctness over `StateT Nat Option` is expressed with a bare `signals (_ : Unit) => False`;
the state still needs binders in `requires`/`ensures`. -/
method stateOptionTotal returns (res : Nat) in CounterOption
  requires (s : Nat) => True
  signals (_ : Unit) => False
  ensures (s : Nat) => res = 0
do
  set 0
  return 0

#check stateOptionTotal
prove_correct stateOptionTotal by
  velvet_vcgen [stateOptionTotal] with finish

/- Partial correctness loop over `StateT Nat Option` without termination measure. -/
set_option velvet.semantics.termination "partial" in
method countStatePartial (n : Nat) returns (res : Nat) in CounterOption
    requires (s : Nat) => True
    signals (_ : Unit) => True
    ensures (s : Nat) => res = n ∧ s = n
  do
  set 0
  let mut i := 0
  while' i < n
    invariant state_tracks : (fun s : Nat => s = i ∧ i ≤ n)
    done_with state_done : (fun s : Nat => i = n ∧ s = n)
  do
    i := i + 1
    set i
  return i

#check countStatePartial
prove_correct countStatePartial by
  velvet_vcgen [countStatePartial] with finish

end Velvet.Examples.StateT
