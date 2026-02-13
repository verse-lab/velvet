import Auto
import Lean
import Std.Data.HashMap

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.Options
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Extension
import CaseStudies.Velvet.Syntax

open Lean Elab Command Meta Term in
/-- Run `#eval term` and capture the output message as a string. -/
private def evalAndCapture (t : Syntax) : CommandElabM (String × String) := do
  let termStr := t.reprint.getD "<term>"
  -- Save current messages, run #eval, capture output, restore messages
  let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
  try
    let t' : TSyntax `term := ⟨t⟩
    let evalCmd ← `(command| #eval $t')
    elabCommand evalCmd
    let msgs := (← get).messages
    let output := msgs.toList.filterMap fun msg =>
      if msg.severity == .information then some msg.data else none
    let outputStr ← output.mapM fun md => md.toString
    return (termStr, "\n".intercalate outputStr)
  finally
    modify fun st => { st with messages := initMsgs }

open Lean Elab Command Meta Term in

/--
`#assert_same_evaluation #[term1, term2, ...]` evaluates all terms (via `#eval`) and
asserts they produce identical output. Useful for testing Velvet methods against expected values.

```
#assert_same_evaluation #[1 + 1, 2]
#assert_same_evaluation #[(decodeStr' input).run, expected]
```
-/
elab "#assert_same_evaluation " arr:term : command => do
  let `(#[$ts,*]) := arr
    | throwError "Expected array literal #[term1, term2, ...]"
  let terms := ts.getElems
  if terms.size < 2 then
    throwError "Need at least 2 terms to compare"
  let results ← terms.mapM evalAndCapture
  let (firstTerm, firstResult) := results[0]!
  for i in [1:results.size] do
    let (iTerm, iResult) := results[i]!
    if iResult != firstResult then
      throwError "Evaluations differ!\n\nTerm 1: {firstTerm}\n=> {firstResult}\n\nTerm {i+1}: {iTerm}\n=> {iResult}"


macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := Array.set! $id:term $idx $val )
  | `(doElem|$id:ident[$idx:term] += $val:term) =>
    `(doElem| $id:term := Array.set! $id:term $idx (($id:term)[$idx]! + $val))
  | `(doElem|swap $id1:ident[$idx1:term] $id2:ident[$idx2:term]) =>
    `(doElem|do
      let lhs := $id1:ident[$idx1:term]
      let rhs := $id2:ident[$idx2:term]
      $id1:ident[$idx1] := rhs
      $id2:ident[$idx2] := lhs)
  | `(doElem|swap! $id1:ident[$idx1:term]! $id2:ident[$idx2:term]!) =>
    `(doElem|do
      let lhs := $id1:ident[$idx1:term]!
      let rhs := $id2:ident[$idx2:term]!
      $id1:ident := ($id1:ident).set! $idx1:term rhs
      $id2:ident := ($id2:ident).set! $idx2:term lhs)

theorem Array.get_set_c [Inhabited α] (i j: Nat) (val: α) (arr: Array α):
  i < arr.size → (arr.set! j val)[i]! = if i = j then val else arr[i]! := by
    intro h
    by_cases h' : j < arr.size
    { simp [Array.setIfInBounds, dif_pos h']
      rw [getElem!_pos, getElem!_pos] <;> try simp [*]
      rw [@Array.getElem_set]; aesop }
    simp [Array.setIfInBounds, dif_neg h']
    rw [getElem!_pos] <;> try simp [*]
    omega

attribute [grind =]
  Array.get_set_c

lemma add_mod_elim (m n: Nat) {a b : Nat} (hm: m > 0) (h: (a + n) % m = (b + n) % m): a % m = b % m := by
  nth_rw 1 [←Nat.add_mod_mod] at h
  nth_rw 2 [←Nat.add_mod_mod] at h
  have hyp := Nat.add_mod_eq_add_mod_right (m - n % m) h
  repeat rw [add_assoc] at hyp
  have : n % m + (m - n % m) = m := by
    rw [←Nat.add_sub_assoc, Nat.add_sub_cancel_left]
    have lem := Nat.mod_lt n hm
    omega
  simp [this] at hyp
  exact hyp

def Array.toMultiset (arr : Array α) := Multiset.ofList arr.toList

theorem Array.multiset_swap [Inhabited α]
(arr: Array α) (idx₁ idx₂: Nat) (h_idx₁: idx₁ < arr.size) (h_idx₂: idx₂ < arr.size) :
  ((arr.set! idx₂ arr[idx₁]!).set! idx₁ arr[idx₂]!).toMultiset = arr.toMultiset := by
    classical
    simp [List.perm_iff_count, Array.toMultiset]
    intro a;
    rw [getElem!_pos,getElem!_pos] <;> try simp [*]
    rw [List.count_set] <;> try simp [*]
    rw [List.count_set] <;> try simp [*]
    simp [List.getElem_set]
    split_ifs with h <;> try simp
    have : Array.count a arr > 0 := by
      apply Array.count_pos_iff.mpr; simp [<-h]
    omega

@[grind]
lemma lemma_2 [Inhabited α] (s : List α) (x : α) :
  (∀ i : Nat, i < s.length -> s[i]! ≠ x) -> ¬ x ∈ s := by
  intro h hx
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
  exact h i hi (by rw [getElem!_pos s i hi, hix])
