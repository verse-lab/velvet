import CaseStudies.Velvet.Std
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    toLowercase: Convert all uppercase characters in a string to their lowercase equivalents.
    Natural language breakdown:
    1. Input is any string s (no preconditions).
    2. Output is a string result with the same length as s.
    3. For every character position i in s, the output character at i equals Char.toLower applied to the input character at i.
    4. Characters not affected by Char.toLower remain unchanged.
-/

section Specs
-- Helper: Pointwise character relation between two strings via their underlying Char lists.
-- This characterizes the output uniquely without referring to List Char.toLower.
-- Note: Char.toLower converts uppercase ASCII letters 'A'..'Z' to lowercase and leaves other chars unchanged.
@[grind]
def charsLoweredPointwise (s : List Char) (t : List Char) : Prop :=
  t.length = s.length ∧
    ∀ (i : Nat), i < s.length → t[i]! = Char.toLower (s[i]!)

def precondition (s : List Char) : Prop :=
  True

@[grind]
def postcondition (s : List Char) (result : List Char) : Prop :=
  charsLoweredPointwise s result
end Specs

section Impl
method toLowercase (s: List Char)
  return (result: List Char)
  require precondition s
  ensures postcondition s result
  do
  let sl := s
  let mut tl : List Char := []
  let mut i : Nat := 0
  while i < sl.length
    -- i stays within bounds of the source list
    -- init: i=0; step: i:=i+1; exit: i=sl.length
    invariant "inv_bounds" i ≤ sl.length
    -- tl is exactly the lowered prefix of sl of length i
    -- init: tl=[] and i=0; step: append lowered sl[i]!
    invariant "inv_tl_length" tl.length = i
    invariant "inv_tl_pointwise" (∀ j : Nat, j < i → tl[j]! = Char.toLower (sl[j]!))
    done_with i = sl.length
  do
    let c := sl[i]!
    tl := tl ++ [Char.toLower c]
    i := i + 1
  let resStr := tl
  return resStr
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct toLowercase by
  loom_solve <;> (try simp at *; expose_names)

end Proof
