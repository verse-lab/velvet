import CaseStudies.Velvet.Std
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    elementWiseModulo: compute the element-wise modulo (remainder) between two arrays of integers.
    Natural language breakdown:
    1. Inputs are two arrays a and b of integers.
    2. The two arrays must have the same length.
    3. Every element of b must be non-zero so that the modulo operation is defined.
    4. The output is a new array result of integers.
    5. The output has the same length as the input arrays.
    6. For each valid index i, the output element result[i] equals a[i] % b[i].
    7. "Non-null" arrays are implicit in Lean: an Array value always exists, so there is no null case.
-/

section Specs
-- Helper predicate: all entries of an Int array are non-zero.
-- We phrase it pointwise with safe access `b[i]!` guarded by `i < b.size`.
abbrev allNonzero (b : Array Int) : Prop :=
  ∀ (i : Nat), i < b.size → b[i]! ≠ 0

-- Preconditions:
-- 1) Same length
-- 2) No zero divisor in b
-- Note: "non-null" is not meaningful in Lean; arrays are always defined values.
abbrev precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size ∧ allNonzero b

-- Postconditions:
-- 1) Result length equals input length.
-- 2) Pointwise remainder property.
abbrev postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
    (∀ (i : Nat), i < a.size → result[i]! = a[i]! % b[i]!)
end Specs

section Impl
method elementWiseModulo (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  let mut result := Array.replicate a.size 0
  let mut i : Nat := 0
  while i < a.size
    -- i stays within array bounds; needed for safe indexing and loop exit reasoning.
    -- Init: i=0; Preserved: i increments by 1 while i<a.size; Exit: i=a.size.
    invariant "ewm_idx_bounds" i ≤ a.size
    -- The accumulator array keeps the correct size.
    -- Init: replicate has size a.size; Preserved: set! preserves size.
    invariant "ewm_result_size" result.size = a.size
    -- Elements already processed (k < i) satisfy the modulo specification.
    -- Init: vacuous for i=0; Preserved: set! updates index i, leaving <i untouched.
    -- Exit with i=a.size gives the full postcondition.
    invariant "ewm_prefix_correct" (∀ (k : Nat), k < i → result[k]! = a[k]! % b[k]!)
    done_with i = a.size
  do
    -- Safe since i < a.size and a.size = b.size from precondition
    result := result.set! i (a[i]! % b[i]!)
    i := i + 1
  return result
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct elementWiseModulo by
  loom_solve <;> (try simp at *; expose_names)
end Proof
