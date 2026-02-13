import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isSublist: decide whether `sub` appears as a contiguous block inside `main`.
    Natural language breakdown:
    1. Input consists of two lists of integers: `sub` and `main`.
    2. `sub` appears in `main` as a contiguous sequence iff there exist lists `pre` and `suf`
       such that `main = pre ++ sub ++ suf`.
    3. The method returns `true` exactly when `sub` is a contiguous sublist (infix) of `main`.
    4. The empty list is a contiguous sublist of every list, including the empty list.
    5. If `main` is empty and `sub` is nonempty, the answer is `false`.
    6. There are no preconditions.
-/

-- Helper predicate: `sub` is a contiguous sublist (infix) of `main`.
-- Mathlib/Lean provides `List.IsInfix` with notation `<:+:`.
@[grind]
def isContiguousSublist (sub : List Int) (main : List Int) : Prop :=
  sub <:+: main
section Impl
method isSublist (sub : List Int) (main : List Int)
  return (result : Bool)
  ensures result = true ↔ isContiguousSublist sub main
  do
    -- Empty list is an infix of any list.
    if sub = [] then
      return true
    else
      let mut rest := main
      let mut found := false
      while (rest ≠ [] ∧ found = false)
        -- Invariant 1: `rest` is always an infix of the original `main`.
        -- Init: rest = main.
        -- Preserved: dropping 1 element from a list preserves being an infix of the original.
        invariant "rest_infix_of_main" rest <:+: main
        -- Invariant 2: Soundness of `found`: if we ever set it to true, then `sub` is indeed an infix of `main`.
        -- Init: found = false, so vacuously true. Preserved: only set to true when sub = rest.take sub.length,
        -- and since rest is an infix of main, a prefix of rest is also an infix of main.
        invariant "found_sound" (found = true → sub <:+: main)
        -- Invariant 3: Completeness w.r.t. current suffix: if `sub` is an infix of `main`, then either we already found it
        -- or it is still an infix of the remaining `rest` (some later start position).
        -- Init: rest = main, found = false. Preserved: if not found at current head position, rest := rest.drop 1.
        invariant "not_missed" (sub <:+: main → found = true ∨ sub <:+: rest)
        done_with (rest = [] ∨ found = true)
      do
        -- If sub is longer than remaining suffix, it cannot match here.
        if sub.length ≤ rest.length then
          if sub = rest.take sub.length then
            found := true
          else
            rest := rest.drop 1
        else
          rest := rest.drop 1
      return found
end Impl

section Proof
set_option maxHeartbeats 10000000

attribute [grind] List.singleton_append List.append_assoc List.take_prefix List.IsPrefix.isInfix List.take_left

prove_correct isSublist by
  loom_solve; simp at * 
  intro hmain
  rcases invariant_not_missed hmain with (_|⟨pre, suf, hpre⟩) <;> try grind
  have hpre_ne_nil : pre ≠ [] := by grind
  grind
