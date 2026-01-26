import CaseStudies.Velvet.Std
import Mathlib.Data.String.Basic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    replaceChars: Replace every occurrence of a specified character in a string.
    Natural language breakdown:
    1. Inputs are a string s and two characters oldChar and newChar.
    2. The result is a string with the same number of characters as s.
    3. For each index i within bounds, if the i-th character of s equals oldChar,
       then the i-th character of the result equals newChar.
    4. For each index i within bounds, if the i-th character of s does not equal oldChar,
       then the i-th character of the result equals the i-th character of s.
    5. There are no preconditions; the method must work for any string and characters.
-/

section Specs
-- Helper: pointwise replacement on characters.
-- This is a simple, computable predicate used in the postcondition.
@[grind]
def replChar (oldChar : Char) (newChar : Char) (c : Char) : Char :=
  if c = oldChar then newChar else c

-- No preconditions.
def precondition (s : Array Char) (oldChar : Char) (newChar : Char) : Prop :=
  True

-- Postcondition: list-view length preserved and pointwise replacement behavior on `toList`.
-- We specify everything through `toList` to avoid mixing different views (`Array Char.length` vs list length).
@[grind]
def postcondition (s : Array Char) (oldChar : Char) (newChar : Char) (result : Array Char) : Prop :=
  result.size = s.size ∧
  (∀ (i : Nat), i < s.size →
    result[i]! = replChar oldChar newChar (s[i]!))
end Specs

section Impl
method replaceChars (s : Array Char) (oldChar : Char) (newChar : Char)
  return (result : Array Char)
  require precondition s oldChar newChar
  ensures postcondition s oldChar newChar result
  do
  let chars := s
  let mut out : Array Char := #[]
  let mut i : Nat := 0
  while i < chars.size
    -- i stays within bounds of `chars`.
    -- Init: i = 0. Preserved: i increases by 1 while guard enforces i < chars.length.
    invariant "inv_bounds" i ≤ chars.size
    -- `out` is the result of pointwise replacement on the prefix processed so far.
    -- Init: i=0, out="". Preserved: we append exactly replChar(...) of chars[i]!
    -- Suffices: at exit i=chars.length, we have full list processed.
    invariant "inv_out_list" out = (Array.map (replChar oldChar newChar) (chars.take i))
  do
    let c := chars[i]!
    let c' := replChar oldChar newChar c
    out := out.push c'
    i := i + 1
  return out
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct replaceChars by
  loom_solve <;> (try simp at *; expose_names)

end Proof
