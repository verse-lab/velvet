import CaseStudies.Velvet.Std
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    removeElement: remove the element at index k from an array of integers.
    Natural language breakdown:
    1. Inputs are an integer array s and a natural number k (0-indexed).
    2. k is assumed to be a valid index, i.e., 0 ≤ k < s.size.
    3. The output is an array containing all elements of s except the one at index k.
    4. Elements before index k are unchanged and keep their positions.
    5. Elements after index k are shifted left by one position.
    6. The output array has size exactly s.size - 1.
-/

section Specs
-- Helper: describe the element-wise relationship between input and output after removing index k.
-- For output index i:
-- * if i < k, output[i] = s[i]
-- * if i ≥ k, output[i] = s[i+1]

abbrev precondition (s : Array Int) (k : Nat) : Prop :=
  k < s.size

abbrev postcondition (s : Array Int) (k : Nat) (result : Array Int) : Prop :=
  result.size + 1 = s.size ∧
  (∀ (i : Nat), i < result.size →
      (if i < k then result[i]! = s[i]! else result[i]! = s[i + 1]!))
end Specs

section Impl
method removeElement (s : Array Int) (k : Nat)
  return (result : Array Int)
  require precondition s k
  ensures postcondition s k result
  do
  let mut result := Array.replicate (s.size - 1) (0:Int)
  let mut i : Nat := 0
  while i < result.size
    -- Bounds: i is within result indices; initialization i=0, preservation by i:=i+1 under loop guard.
    invariant "inv_i_le" i ≤ result.size
    -- Result size is fixed and matches specification: since k < s.size, we have s.size > 0 so (s.size - 1) is well-defined.
    invariant "inv_res_size" result.size + 1 = s.size
    -- Prefix correctness: all already-filled positions satisfy the remove-at-k relationship.
    invariant "inv_prefix" ∀ (j : Nat), j < i →
      (if j < k then result[j]! = s[j]! else result[j]! = s[j + 1]!)
  do
    if i < k then
      result := result.set! i (s[i]!)
    else
      result := result.set! i (s[i + 1]!)
    i := i + 1
  return result
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct removeElement by
  loom_solve <;> (try simp at *; expose_names)
end Proof
