module

prelude
public import Velvet
public meta import Velvet

open Velvet.Testing

section DecidableSynthesisTests

example (n : Nat) (a : Array Nat) :
  Decidable (∀ i, i < n → a.size > 0) := by
  infer_aux_decidable_instance
  infer_instance

example (n : Nat) (a : Array Nat) :
  Decidable (∃ i, i < n ∧ a.size > 0) := by
  infer_aux_decidable_instance
  infer_instance

example (lo hi : Int) (a : Array Int) :
  Decidable (∀ r, lo ≤ r → r ≤ hi → a.size > 0) := by
  infer_aux_decidable_instance
  infer_instance

example (lo hi : Int) (a : Array Int) :
  Decidable (∃ r, lo ≤ r ∧ r ≤ hi ∧ a.size > 0) := by
  infer_aux_decidable_instance
  infer_instance

@[velvetAbstractionSimp]
def boundedCheck (arr : Array Int) (max : Int) : Prop :=
  ∀ i, i < arr.size → arr[i]! ≤ max

example (arr : Array Int) (max : Int) :
  Decidable (boundedCheck arr max) := by
  infer_aux_decidable_instance
  infer_instance

end DecidableSynthesisTests

section MethodTesting

set_option velvet.semantics.termination "total" in
method clampVal (x : Int) (lo : Int) (hi : Int) returns (res : Int)
  requires lo_le_hi : lo ≤ hi
  ensures bounded : lo ≤ res ∧ res ≤ hi
  ensures id_in_range : lo ≤ x ∧ x ≤ hi → res = x
do
  if x < lo then return lo
  if x > hi then return hi
  return x

extract_program_for clampVal
prove_precondition_decidable_for clampVal
prove_postcondition_decidable_for clampVal
derive_tester_for clampVal

#test_method clampVal (numTests := 50)

set_option velvet.semantics.termination "total" in
method findFirstPositive (arr : Array Int) returns (res : Option Nat)
  ensures some_pos : ∀ idx, res = some idx → idx < arr.size ∧ arr[idx]! > 0
  ensures none_all_neg : res = none → ∀ idx, idx < arr.size → arr[idx]! ≤ 0
do
  let mut i : Nat := 0
  while' loop_cond : i < arr.size
    invariant i ≤ arr.size
    invariant ∀ j, j < i → arr[j]! ≤ 0
    decreasing arr.size - i
  do
    if arr[i]! > 0 then
      return some i
    i := i + 1
  return none

extract_program_for findFirstPositive
prove_precondition_decidable_for findFirstPositive
prove_postcondition_decidable_for findFirstPositive
derive_tester_for findFirstPositive

#test_method findFirstPositive (numTests := 50)

end MethodTesting


section NonDeterministicTesting

method pickAngelicChoice (n : Nat) returns (res : Nat) in AngelicT Option
  signals (_ : Unit) => False
  ensures res > n
do
  let (diff : Nat) :| diff > 0
  return n + diff

extract_program_for pickAngelicChoice
prove_precondition_decidable_for pickAngelicChoice
prove_postcondition_decidable_for pickAngelicChoice
derive_tester_for pickAngelicChoice

#test_method pickAngelicChoice (numTests := 20)

end NonDeterministicTesting

section CounterexampleDetection

set_option velvet.semantics.termination "total" in
method buggyClamp (x : Int) (lo : Int) (hi : Int) returns (res : Int)
  requires lo ≤ hi
  ensures res > hi
do
  return x

extract_program_for buggyClamp
prove_precondition_decidable_for buggyClamp
prove_postcondition_decidable_for buggyClamp
derive_tester_for buggyClamp

-- Verify that a counterexample is caught and reported
#eval do
  let ok ← Velvet.Testing.velvetQuickCheck "buggyClamp" buggyClampTester 20
  if ok then
    throw <| IO.userError "Expected counterexample not found!"

end CounterexampleDetection
