import CaseStudies.Velvet.Std
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    differenceMinMax: compute the difference between the maximum and minimum values of a nonempty array of Int.
    Natural language breakdown:
    1. The input is an array `a : Array Int`.
    2. The input array is assumed to be non-empty.
    3. Let `mn` be the minimum value occurring in `a` and `mx` be the maximum value occurring in `a`.
    4. The returned integer is `mx - mn`.
    5. The result must be 0 when all elements are equal or when the array has exactly one element.
    6. The specification should describe `mn` and `mx` as bounds achieved by some array elements.
-/

section Specs
-- Helper predicate: value occurs in array
abbrev InArray (a : Array Int) (v : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = v

-- Helper predicate: `mn` is a minimum value achieved in the array
abbrev IsMinOfArray (a : Array Int) (mn : Int) : Prop :=
  InArray a mn ∧ (∀ (i : Nat), i < a.size → mn ≤ a[i]!)

-- Helper predicate: `mx` is a maximum value achieved in the array
abbrev IsMaxOfArray (a : Array Int) (mx : Int) : Prop :=
  InArray a mx ∧ (∀ (i : Nat), i < a.size → a[i]! ≤ mx)

-- Precondition: array is nonempty
-- We use `a.size ≠ 0` which is equivalent to `a ≠ #[]` via `Array.size_eq_zero_iff`.
abbrev precondition (a : Array Int) : Prop :=
  a.size ≠ 0

-- Postcondition: result equals (max - min) for some achieved max/min bounds.
-- We avoid specifying an algorithm; instead we characterize the unique value via existence of
-- extremal witnesses and defining equation.
abbrev postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (mn : Int) (mx : Int),
    IsMinOfArray a mn ∧
    IsMaxOfArray a mx ∧
    result = mx - mn
end Specs

section Impl
method differenceMinMax (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
    let mut mn := a[0]!
    let mut mx := a[0]!

    let mut i : Nat := 1
    while i < a.size
      -- Invariant: index stays within bounds (initially i=1; preserved by i := i+1; needed to justify accesses and to cover all elements on exit)
      invariant "diffMinMax_i_bounds" 1 ≤ i ∧ i ≤ a.size
      -- Invariant: mn is a minimum among the elements seen so far (0..i-1), and is achieved in that prefix
      -- Initialization: mn=a[0]! witnessed by j=0; Preservation: updating mn to v maintains min property; Sufficient with i=a.size to get global min.
      invariant "diffMinMax_mn_prefix_min" (∃ j : Nat, j < i ∧ a[j]! = mn) ∧ (∀ j : Nat, j < i → mn ≤ a[j]!)
      -- Invariant: mx is a maximum among the elements seen so far (0..i-1), and is achieved in that prefix
      -- Initialization: mx=a[0]! witnessed by j=0; Preservation: updating mx to v maintains max property; Sufficient with i=a.size to get global max.
      invariant "diffMinMax_mx_prefix_max" (∃ j : Nat, j < i ∧ a[j]! = mx) ∧ (∀ j : Nat, j < i → a[j]! ≤ mx)
    do
      let v := a[i]!
      if v < mn then
        mn := v
      else
        pure ()
      if v > mx then
        mx := v
      else
        pure ()
      i := i + 1

    return (mx - mn)
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct differenceMinMax by
  loom_solve <;> (try simp at *; expose_names)
end Proof
