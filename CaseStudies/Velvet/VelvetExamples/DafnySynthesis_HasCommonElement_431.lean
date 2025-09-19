import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 2
set_option auto.smt.solver.name "cvc5"

--method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    --requires a != null && b != null
    --ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    --ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
--{
    --result := false;
    --for i := 0 to a.Length
        --invariant 0 <= i <= a.Length
        --invariant !result ==> forall k, j :: 0 <= k < i && 0 <= j < b.Length ==> a[k] != b[j]
    --{
        --for j := 0 to b.Length
            --invariant 0 <= j <= b.Length
            --invariant !result ==> forall k :: 0 <= k < j ==> a[i] != b[k]
        --{
            --if a[i] == b[j] {
                --result := true;
                --return;
            --}
        --}
    --}
--}

/- method getCommonElement  -/


-- TODO: Needs reworking, issue happening due to lack of support for early return in Velvet i guess, need to reframe is somehow
method HasCommonElement (a: Array Int) (b: Array Int) return (result: Option (Nat × Nat))
    ensures result.isSome -> a[result.get!.fst ]! = b[result.get!.snd]!
    ensures result.isNone ->  forall i j , 0 <= i ∧ i  < a.size ∧ 0 <= j ∧ j < b.size -> a[i]! != b[j]!
    do
    let mut result := Option.none
    let mut i := 0
    let mut j := 0
    while i < a.size ∧ result.isNone
        invariant 0 <= i ∧ i <= a.size
        invariant result.isNone ->  forall k j , 0 <= k ∧ k  < i ∧ 0 <= j ∧ j < b.size -> a[k]! != b[j]!
        do 
        j := 0
        while j < b.size ∧ result.isNone
            invariant 0 <= j ∧ j <= b.size
            invariant result.isNone  -> forall k , 0 <= k ∧ k < j -> a[i]! != b[k]!
            done_with j = b.size
            do
            if a[i]! = b[j]! then
                result := Option.some ⟨i, j⟩
            j := j + 1
      i := i + 1
    return result

prove_correct HasCommonElement by
  unfold HasCommonElement
  loom_solve
  · grind
  · grind
  · sorry
  · sorry

