import CaseStudies.Velvet.Std
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    toUppercase: Convert a string to uppercase.
    Natural language breakdown:
    1. Input is a string s.
    2. Output is a string result.
    3. The output has the same length as the input.
    4. For every position i within bounds, the i-th character of result equals
       the uppercase of the i-th character of s.
    5. Uppercasing is performed using Char.toUpper: lowercase ASCII letters are
       mapped to their corresponding uppercase letters; all other characters are unchanged.
    6. There are no preconditions.
-/
section Impl
method toUppercase (s: Array Char)
  return (result: Array Char)
  ensures result.size = s.size
  ensures ∀ (i : Nat), i < s.size → result[i]! = (s[i]!).toUpper
  do
  let chars := s
  let mut out : Array Char := #[]
  let mut i : Nat := 0
  while i < chars.size
    -- i stays within bounds of chars, giving safe indexing and enabling exit reasoning
    invariant "inv_bounds" i ≤ chars.size
    -- out is exactly the mapped prefix (toUpper) of the first i characters of chars
    -- initialization: i=0, out=[] = map ... []
    -- preservation: body appends toUpper(chars[i]) matching map over take (i+1)
    invariant "inv_out_prefix" out = (Array.map (fun c => c.toUpper) (chars.take i))
    -- length of out tracks progress and will match final string length
    invariant "inv_len" out.size = i
    done_with (i = chars.size)
  do
    out := out.push chars[i]!.toUpper
    i := i + 1
  let res := out
  return res
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct toUppercase by
  loom_solve <;> (try simp at *; expose_names)

end Proof
