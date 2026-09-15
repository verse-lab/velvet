module

public import Velvet
public meta import Velvet
public import Velvet.Examples.StateT
public meta import Velvet.Examples.StateT

open Velvet.Testing

namespace Velvet.Examples.Testing

method increment (x : Nat) returns (result : Nat) in StateM Nat
  given (initial : Nat)
  requires (s : Nat) => s = initial ∧ s + x ≤ 100
  ensures (s : Nat) => result = initial ∧ s = initial + x
do
  let old ← get
  set (old + x)
  return old

prove_precondition_decidable_for increment
prove_postcondition_decidable_for increment
#derive_tester_for increment

example : Nat → Nat → Nat → TestVerdict := increment.check
#guard increment.check 5 20 20 == .pass
#guard increment.check 5 99 99 == .discard

method brokenIncrement (x : Nat) returns (result : Nat) in StateM Nat
  given (initial : Nat)
  requires (s : Nat) => s = initial
  ensures (s : Nat) => result = initial ∧ s = initial + x
do
  let old ← get
  set (old + x + 1)
  return old

#derive_tester_for brokenIncrement
#guard brokenIncrement.check 5 20 20 == .fail

public abbrev Stack := StateT Nat (StateT Bool (ReaderT Nat Id))

method stacked (x : Nat) returns (result : Nat) in Stack
  requires (s : Nat) (_ : Bool) (limit : Nat) => s + x ≤ limit
  ensures (s : Nat) (flag : Bool) (limit : Nat) => result = s ∧ flag ∧ s ≤ limit
do
  let s ← getThe Nat
  set (s + x)
  set true
  return s + x

#derive_tester_for stacked
example : Nat → Nat → Bool → Nat → TestVerdict := stacked.check
#guard stacked.check 3 4 false 10 == .pass
#guard stacked.check 3 9 false 10 == .discard

method checked (bad : Bool) returns (result : Nat) in ExceptT String (StateT Nat Option)
  requires (s : Nat) => s < 100
  signals (e : String) (s : Nat) => e = "bad" ∧ s = 42
  signals False
  ensures (s : Nat) => result = s
do
  set 42
  if bad then throw "bad"
  return 42

prove_signals_decidable_for checked
#derive_tester_for checked
#guard checked.check true 0 == .pass
#guard checked.check false 0 == .pass

method boundedArray (arr : Array Nat) returns (result : Nat) in StateM Nat
  requires (bound : Nat) => ∀ i, 0 ≤ i ∧ i < arr.size → arr[i]! ≤ bound
  ensures (s : Nat) => ∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ s
do
  return arr.size

#derive_tester_for boundedArray
#guard boundedArray.check #[1, 2, 3] 3 == .pass
#guard boundedArray.check #[1, 4, 3] 3 == .discard

method integerRange (lo hi : Int) returns (result : Int) in Id
  requires ∀ i : Int, lo ≤ i → i ≤ hi → i < hi + 1
  ensures result = lo
do
  return lo

#derive_tester_for integerRange
#guard integerRange.check (-3) 4 == .pass

method integerWitness (lo hi : Int) returns (result : Int) in Id
  requires ∃ i : Int, lo ≤ i ∧ i ≤ hi ∧ i = lo
  ensures result = lo
do
  return lo

#derive_tester_for integerWitness
#guard integerWitness.check (-3) 4 == .pass
#guard integerWitness.check 4 (-3) == .discard

method customDecision (x : Nat) returns (result : Nat) in Id
  requires ∀ n : Nat, x ≤ x + n
  ensures result = x
do
  return x

prove_precondition_decidable_for customDecision by
  exact isTrue (fun n => Nat.le_add_right x n)
#derive_tester_for customDecision
#guard customDecision.check 8 == .pass

/-- Withdrawal is possible when there is a natural-number balance left afterward. -/
public def CanWithdraw (amount balance : Nat) : Prop :=
  ∃ remaining : Nat, balance = amount + remaining

method withdraw (amount : Nat) returns (remaining : Nat) in StateM Nat
  given (initial : Nat)
  requires (balance : Nat) => balance = initial ∧ CanWithdraw amount balance
  ensures (balance : Nat) => balance = remaining ∧ remaining + amount = initial
do
  let balance ← get
  let remaining := balance - amount
  set remaining
  return remaining

-- The command introduces `amount initial balance` and simplifies assertion wrappers.
-- Its goal is `Decidable (balance = initial ∧ CanWithdraw amount balance)`.
prove_precondition_decidable_for withdraw by
  letI : Decidable (CanWithdraw amount balance) := by
    by_cases h : amount ≤ balance
    · apply isTrue
      unfold CanWithdraw
      exact ⟨balance - amount, by omega⟩
    · apply isFalse
      intro ⟨remaining, hbalance⟩
      omega
  infer_instance

prove_postcondition_decidable_for withdraw by
  infer_instance

#derive_tester_for withdraw
#guard withdraw.check 3 10 10 == .pass
#guard withdraw.check 11 10 10 == .discard
#guard withdraw.check 3 10 8 == .discard

method explicitFailure returns (result : Nat)
  requires True
  ensures result = 0
do
  failure

#derive_tester_for explicitFailure
#guard explicitFailure.check == .fail

-- Changing the exception contract changes the verdict for the same outcome.
method permittedFailure returns (result : Nat)
  requires True
  signals True
  ensures result = 0
do
  failure

#derive_tester_for permittedFailure
#guard permittedFailure.check == .pass

-- Unit is still a real exception value for Except Unit, unlike Option failure.
method unitException returns (result : Nat) in Except Unit
  requires True
  signals (e : Unit) => e = ()
  ensures False
do
  throw ()

#derive_tester_for unitException
#guard unitException.check == .pass

method lostState (bad : Bool) returns (result : Nat) in StateT Nat (Except String)
  requires (s : Nat) => s < 100
  signals (e : String) => e = "bad"
  ensures (s : Nat) => result = s
do
  set 42
  if bad then throw "wrong"
  return 42

#derive_tester_for lostState
#guard lostState.check true 0 == .fail
#guard lostState.check false 0 == .pass

method identity {α : Type} [DecidableEq α] (x : α) returns (result : α) in Id
  requires True
  ensures result = x
do
  return x

#derive_tester_for identity
#guard identity.check "hello" == .pass

method dependent (n : Nat) (x : Fin (n + 1)) returns (result : Nat) in ReaderT Nat Id
  requires (env : Nat) => x.val ≤ env
  ensures (env : Nat) => result ≤ env
do
  return x.val

#derive_tester_for dependent
#guard dependent.check 4 ⟨3, by omega⟩ 3 == .pass
#guard dependent.check 4 ⟨3, by omega⟩ 2 == .discard

-- A false precondition must prevent execution, even when the program does not terminate.
method rec rejected (n : Nat) returns (result : Nat)
  requires False
  ensures True
do
  rejected n

#derive_tester_for rejected
#guard rejected.check 0 == .discard

method optional (present : Bool) returns (result : Nat) in OptionT (ReaderT Nat Option)
  requires (env : Nat) => env < 10
  signals (env : Nat) => env = 0
  signals False
  ensures (env : Nat) => result = env
do
  if present then return ← read
  failure

#derive_tester_for optional
#guard optional.check true 4 == .pass
#guard optional.check false 0 == .pass
#guard optional.check false 4 == .fail

method errorState (bad : Bool) returns (result : Nat) in EStateM String Nat
  requires (s : Nat) => s < 10
  signals (e : String) (s : Nat) => e = "bad" ∧ s = 7
  ensures (s : Nat) => result = s
do
  set 7
  if bad then throw "bad"
  return 7

#derive_tester_for errorState
#guard errorState.check true 0 == .pass
#guard errorState.check false 0 == .pass

-- A caller can supply inputs from any source; the checker has no generator dependency.
example : List TestVerdict :=
  [(5, 20), (5, 99)].map fun (x, s) => increment.check x s s

-- Derive from imported metadata, without placing declarations in the caller's namespace.
#derive_tester_for Velvet.Examples.StateT.incrementBy
#guard Velvet.Examples.StateT.incrementBy.check 5 20 20 == .pass

section AlternativeWP

-- A direct WP instance can override the one from WPMonad. Do not silently test a
-- different interpretation, even when both have the same assertion types.
@[instance_reducible] public def alternativeWP : Std.Internal.Do.WP (Id Nat) Nat Prop Std.Internal.Do.EPost.Nil where
  wpTrans _ := ⟨fun _ _ => True⟩
  wp_trans_monotone _ := fun _ _ _ _ _ _ => id

attribute [local instance] alternativeWP

method alternative returns (result : Nat) in Id
  requires True
  ensures False
do
  return 0

/-- error: DecidableWP does not match this method's WP interpretation -/
#guard_msgs in
#derive_tester_for alternative

end AlternativeWP

end Velvet.Examples.Testing
