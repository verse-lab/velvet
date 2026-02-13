import Auto
import Lean

import Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver "cvc5"
set_option loom.solver.smt.timeout 5

-- Helper: check if a character is a decimal digit
def isDigit (c: Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

-- Helper: check if result appears as a contiguous substring at position pos in input
def appearsAt (input result: Array Char) (pos: Nat) : Prop :=
  pos + result.size ≤ input.size ∧
  ∀ i, i < result.size → input[pos + i]! = result[i]!

method LeftmostMaximalDigit (input: Array Char)
  return (result: Array Char)
  ensures result.size > 0 → ∀ pos, appearsAt input result pos →
    ∀ pos', pos' < pos →
      ¬(pos' + result.size ≤ input.size ∧
        (∀ i, i < result.size → isDigit input[pos' + i]!) ∧
        (pos' = 0 ∨ ¬isDigit input[pos' - 1]!) ∧
        (pos' + result.size = input.size ∨ ¬isDigit input[pos' + result.size]!))
  do
  let mut i: Nat := 0
  let mut currentStart: Nat := 0
  let mut currentLen: Nat := 0
  let mut bestStart: Nat := 0
  let mut bestLen: Nat := 0
  let mut inDigitSubstring: Bool := false

  while i < input.size
    -- Invariant 7: Best is maximum among complete maximal substrings in [0..i)
    invariant ∀ pos len,
      (len > 0 ∧
       pos + len ≤ i ∧
       (∀ j, j < len → isDigit input[pos + j]!) ∧
       (pos = 0 ∨ ¬isDigit input[pos - 1]!) ∧
       (pos + len = i ∨ (pos + len < i ∧ ¬isDigit input[pos + len]!))) →
      len ≤ bestLen
  do
    let c := input[i]!

    if isDigit c then
      if inDigitSubstring then
        currentLen := currentLen + 1
      else
        currentStart := i
        currentLen := 1
        inDigitSubstring := true
    else
      if inDigitSubstring then
        if currentLen > bestLen then
          bestStart := currentStart
          bestLen := currentLen

        inDigitSubstring := false
        currentLen := 0

    i := i + 1
  pure (input.extract bestStart (bestStart + bestLen))

set_option maxHeartbeats 3000

/--
error: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (3000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
prove_correct LeftmostMaximalDigit by
  loom_solve
  sorry
