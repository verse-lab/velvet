import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

-- Original Dafny code (with bug - doesn't return true when found):
-- method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
--     ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
-- {
--     if |sub| > |main| {
--         return false;
--     }
--
--     for i := 0 to |main| - |sub| + 1
--         invariant 0 <= i <= |main| - |sub| + 1
--         invariant true <== (exists j :: 0 <= j < i && sub == main[j..j + |sub|])
--     {
--         if sub == main[i..i + |sub|] {
--             result := true;  -- Bug: should return true here
--         }
--     }
--     result := false;
-- }

-- Fixed Velvet version
method IsSublist (sub: Array Int) (main: Array Int) return (result: Bool)
    ensures result = true ↔ (∃ i, 0 ≤ i ∧ i ≤ main.size - sub.size ∧
                            ∀ j, 0 ≤ j ∧ j < sub.size → sub[j]! = main[i + j]!)
    do
    let mut result := false
    if sub.size > main.size then
        result := false
    else
        let mut i := 0
        let mut found := false
        while i ≤ main.size - sub.size ∧ ¬found
            invariant 0 ≤ i ∧ i ≤ main.size - sub.size + 1
            invariant found = false → ¬(∃ j, 0 ≤ j ∧ j < i ∧
                        ∀ k, 0 ≤ k ∧ k < sub.size → sub[k]! = main[j + k]!)
            invariant found = true → (∃ j, 0 ≤ j ∧ j < i ∧
                        ∀ k, 0 ≤ k ∧ k < sub.size → sub[k]! = main[j + k]!)
            done_with i = main.size - sub.size + 1 ∨ found = true
            do
            -- Check if sub matches at position i
            let mut isMatch := true
            let mut j := 0
            while j < sub.size ∧ isMatch
                invariant 0 ≤ j ∧ j ≤ sub.size
                invariant isMatch = true ↔ (∀ k, 0 ≤ k ∧ k < j → sub[k]! = main[i + k]!)
                done_with j = sub.size ∨ isMatch = false
                do
                if sub[j]! ≠ main[i + j]! then
                    isMatch := false
                j := j + 1

            if isMatch then
                found := true

            i := i + 1

        result := found
    return result

attribute [local solverHint] Array.size_replicate Array.size_set

prove_correct IsSublist by
  loom_solve
  sorry -- TODO: Fix the edge case proof
