import Velvet2.Syntax
import Velvet2.Tactics

open Std.Internal.Do

namespace Velvet2.Examples.StateT

abbrev CounterId := StateT Nat Id
abbrev CounterOption := StateT Nat Option
abbrev CounterExceptOption := StateT Nat (ExceptT String Option)

/-- A `StateT Nat Id` loop exercising invariant, decreasing, and done gadgets. -/
def countState (n : Nat) : CounterId Nat := do
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

theorem countState_correct (n : Nat) :
    Triple (countState n)
      (fun _ => True)
      (fun r s => r = n ∧ s = n)
      (⟨⟩ : EPost.Nil) := by
  vcgen' [countState]
  all_goals try simp_all
  name_vcs
  all_goals try simp_all
  all_goals omega

/-- A `StateT Nat Option` program with assertions before and after mutation. -/
def boundedIncrement (limit : Nat) : CounterOption Nat := do
  let current ← get
  assert within_limit : (fun _ : Nat => current < limit)
  set (current + 1)
  assert state_advanced : (fun s : Nat => s = current + 1)
  return current

theorem boundedIncrement_correct (limit : Nat) :
    Triple (boundedIncrement limit)
      (fun s => s < limit)
      (fun current s => current < limit ∧ s = current + 1)
      True := by
  vcgen' [boundedIncrement]
  all_goals simp_all

/-- A finite-range loop over `StateT Nat Option`. -/
def countRange (n : Nat) : CounterOption Nat := do
  set 0
  let mut count := 0
  for' i in 0...n
    invariant range_state : (fun s : Nat => s = i ∧ count = i)
    done_with range_done : (fun s : Nat => s = n ∧ count = n)
  do
    count := i + 1
    set count
  return count

theorem countRange_correct (n : Nat) :
    Triple (countRange n)
      (fun _ => True)
      (fun r s => r = n ∧ s = n)
      True := by
  vcgen' [countRange]
  case range_done =>
    rename_i initial h
    have hl := congrArg List.length h
    simp at hl
    simp_all
  case range_state =>
    rename_i initial current tail h
    have hc := congrArg (fun xs => xs[0]?) h
    simp [Std.Rco.getElem?_toList_eq] at hc
    simp_all
  case vc3 => simp_all
  case range_done =>
    rename_i initial pref current h b state
    have hl := congrArg List.length h
    have hc := congrArg (fun xs => xs[pref.length]?) h
    simp [Std.Rco.getElem?_toList_eq] at hl hc
    simp_all
  case range_state =>
    rename_i initial pref current next tail h b state
    have hc := congrArg (fun xs => xs[pref.length]?) h
    have hn := congrArg (fun xs => xs[pref.length + 1]?) h
    simp [Std.Rco.getElem?_toList_eq] at hc hn
    simp_all

/-- A larger `StateT Nat (ExceptT String Option)` stack. -/
def checkedAdd (delta : Nat) : CounterExceptOption Nat := do
  let current ← get
  if delta = 0 then
    throw "delta must be positive"
  assert positive_delta : (fun _ : Nat => 0 < delta)
  set (current + delta)
  assert state_increased : (fun s : Nat => s = current + delta)
  return current

theorem checkedAdd_correct (delta : Nat) :
    Triple (checkedAdd delta)
      (fun _ => True)
      (fun current s => s = current + delta)
      (⟨fun _ : String => True, True⟩ : EPost.Cons (String → Prop) Prop) := by
  vcgen' [checkedAdd]
  all_goals try simp_all
  all_goals omega

/-- A stateful loop that either reaches `target` or throws at `blocked`. -/
def countUnlessBlocked (target blocked : Nat) : CounterExceptOption Nat := do
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

/--
On success the loop reaches `target`. Since `StateT` is outside `ExceptT`, an
exception has no resulting state, so its postcondition observes only the error.
-/
theorem countUnlessBlocked_correct (target blocked : Nat) :
    Triple (countUnlessBlocked target blocked)
      (fun _ => True)
      (fun result state => result = target ∧ state = target)
      (⟨fun error : String => error = "blocked", True⟩ :
        EPost.Cons (String → Prop) Prop) := by
  vcgen' [countUnlessBlocked]
  all_goals try simp_all
  name_vcs
  all_goals try simp_all
  all_goals omega

/-- `StateT` outside `ReaderT`; assertions have shape `Nat → Nat → Prop`. -/
abbrev ReaderCounter := StateT Nat (ReaderT Nat Id)

/-- Count from the initial state up to the reader-provided limit. -/
def countToReaderLimit : ReaderCounter Nat := do
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
theorem countToReaderLimit_correct :
    Triple countToReaderLimit
      (fun state limit => state ≤ limit)
      (fun result state limit => result = limit ∧ state = limit)
      (⟨⟩ : EPost.Nil) := by
  vcgen' [countToReaderLimit]
  all_goals try simp_all
  name_vcs
  all_goals try simp_all
  all_goals omega

/-- The triangular number `0 + 1 + ... + n`. -/
def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)

/-- Add `1 + ... + limit` from the reader environment to the initial state. -/
def addToReaderLimit : ReaderCounter Nat := do
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
theorem addToReaderLimit_correct :
    Triple addToReaderLimit
      (fun initial limit => initial ≤ limit)
      (fun initial final limit =>
        initial ≤ limit ∧ final = initial + triangular limit)
      (⟨⟩ : EPost.Nil) := by
  vcgen' [addToReaderLimit]
  all_goals try simp_all [triangular]
  name_vcs
  all_goals try simp_all
  case additions_remaining => omega
  case accumulated_sum =>
    constructor
    · simp [Nat.add_assoc]
    · omega
  case all_added =>
    rename_i initial limit pre i state environment stopped
    have hi : i = limit := by omega
    subst i
    simp

end Velvet2.Examples.StateT
