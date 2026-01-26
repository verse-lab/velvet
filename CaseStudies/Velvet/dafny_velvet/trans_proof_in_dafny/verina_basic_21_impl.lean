import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

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

section Specs
-- Helper predicate: `sub` is a contiguous sublist (infix) of `main`.
-- Mathlib/Lean provides `List.IsInfix` with notation `<:+:`.
def isContiguousSublist (sub : List Int) (main : List Int) : Prop :=
  sub <:+: main

-- No preconditions.
def precondition (sub : List Int) (main : List Int) : Prop :=
  True

-- The Boolean result agrees with the infix predicate.
def postcondition (sub : List Int) (main : List Int) (result : Bool) : Prop :=
  result = true ↔ isContiguousSublist sub main
end Specs

section Impl
method isSublist (sub : List Int) (main : List Int)
  return (result : Bool)
  require precondition sub main
  ensures postcondition sub main result
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


-- prove_correct isSublist by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (sub : List ℤ)
    (main : List ℤ)
    (if_pos : sub = [])
    : postcondition sub main true := by
  unfold postcondition
  simp [isContiguousSublist, if_pos, List.nil_infix]

theorem goal_1
    (sub : List ℤ)
    (main : List ℤ)
    (found : Bool)
    (rest : List ℤ)
    (invariant_rest_infix_of_main : rest <:+: main)
    (if_pos_1 : sub = List.take sub.length rest)
    : sub <:+: main := by
    have hpre : sub <+: rest := by
      -- use the characterization of prefix via take
      have : sub = List.take sub.length rest := if_pos_1
      exact (List.prefix_iff_eq_take).2 this
    have hinfix_rest : sub <:+: rest := List.IsPrefix.isInfix hpre
    exact List.IsInfix.trans hinfix_rest invariant_rest_infix_of_main

theorem goal_2
    (sub : List ℤ)
    (main : List ℤ)
    (found : Bool)
    (rest : List ℤ)
    (invariant_rest_infix_of_main : rest <:+: main)
    (invariant_not_missed : sub <:+: main → found = true ∨ sub <:+: rest)
    (a : ¬rest = [])
    (if_pos : sub.length ≤ rest.length)
    (if_neg_1 : ¬sub = List.take sub.length rest)
    : rest.tail <:+: main := by
  rcases invariant_rest_infix_of_main with ⟨pre, suf, hmain⟩
  rcases List.exists_cons_of_ne_nil (l := rest) a with ⟨x, xs, rfl⟩
  -- hmain : pre ++ (x :: xs) ++ suf = main
  refine ⟨pre ++ [x], suf, ?_⟩
  -- show (pre ++ [x]) ++ xs ++ suf = main
  -- rewrite using hmain and associativity
  simpa [List.append_assoc] using hmain

theorem goal_3
    (sub : List ℤ)
    (main : List ℤ)
    (found : Bool)
    (rest : List ℤ)
    (invariant_not_missed : sub <:+: main → found = true ∨ sub <:+: rest)
    (if_neg_1 : ¬sub = List.take sub.length rest)
    : sub <:+: main → found = true ∨ sub <:+: rest.tail := by
  intro hmain
  have hnm : found = true ∨ sub <:+: rest := invariant_not_missed hmain
  cases hnm with
  | inl hfound =>
      exact Or.inl hfound
  | inr hinfix_rest =>
      rcases hinfix_rest with ⟨pre, suf, hpre⟩
      -- hpre : pre ++ sub ++ suf = rest
      have hpre_ne_nil : pre ≠ [] := by
        intro hpre_nil
        subst hpre_nil
        have ht : sub = List.take sub.length rest := by
          -- rest = sub ++ suf
          have : rest = sub ++ suf := by
            simpa [List.append_assoc] using (Eq.symm hpre)
          -- take length sub of (sub ++ suf) = sub
          simpa [this] using (List.take_left (l₁ := sub) (l₂ := suf))
        exact if_neg_1 ht
      rcases List.exists_cons_of_ne_nil hpre_ne_nil with ⟨x, pre', rfl⟩
      -- Now hpre : (x :: pre') ++ sub ++ suf = rest
      refine Or.inr ?_
      refine ⟨pre', suf, ?_⟩
      -- show pre' ++ sub ++ suf = rest.tail
      -- Use tail_append_of_ne_nil on xs = (x :: pre')
      have : (rest.tail) = pre' ++ sub ++ suf := by
        -- take tail of both sides of hpre
        have ht : ((x :: pre') ++ (sub ++ suf)).tail = rest.tail := by
          simpa [List.append_assoc] using congrArg List.tail (by simpa [List.append_assoc] using hpre)
        -- simplify tail of LHS
        -- (x :: pre') ++ (sub ++ suf) = x :: (pre' ++ (sub ++ suf))
        -- so tail is pre' ++ (sub ++ suf)
        simpa [List.append_assoc] using ht.symm
      simpa [this]

theorem goal_4
    (sub : List ℤ)
    (main : List ℤ)
    (found : Bool)
    (rest : List ℤ)
    (invariant_rest_infix_of_main : rest <:+: main)
    (invariant_not_missed : sub <:+: main → found = true ∨ sub <:+: rest)
    (a : ¬rest = [])
    (if_neg_1 : rest.length < sub.length)
    : rest.tail <:+: main := by
  rcases invariant_rest_infix_of_main with ⟨pre, suf, hpre⟩
  rcases List.exists_cons_of_ne_nil a with ⟨x, xs, rfl⟩
  -- hpre : pre ++ (x :: xs) ++ suf = main
  refine ⟨pre ++ [x], suf, ?_⟩
  -- show (pre ++ [x]) ++ xs ++ suf = main
  -- rewrite the middle (x :: xs) as [x] ++ xs and reassociate
  simpa [List.singleton_append, List.append_assoc] using hpre

theorem goal_5
    (sub : List ℤ)
    (main : List ℤ)
    (if_neg : ¬sub = [])
    (found : Bool)
    (rest : List ℤ)
    (invariant_found_sound : found = true → sub <:+: main)
    (invariant_not_missed : sub <:+: main → found = true ∨ sub <:+: rest)
    (done_1 : rest = [] ∨ found = true)
    (i : Bool)
    (rest_1 : List ℤ)
    (i_1 : found = i ∧ rest = rest_1)
    : postcondition sub main i := by
    unfold postcondition isContiguousSublist
    constructor
    · intro hi
      have hfi : found = i := i_1.left
      have hf : found = true := by simpa [hfi] using hi
      exact invariant_found_sound hf
    · intro hsub
      have hfi : found = i := i_1.left
      have hfound_or : found = true ∨ sub <:+: rest := invariant_not_missed hsub
      cases hfound_or with
      | inl hf =>
          simpa [hfi] using hf
      | inr hsub_rest =>
          cases done_1 with
          | inl hrest_nil =>
              have : sub = [] := by
                -- rewrite rest = [] then use infix-of-nil characterization
                apply List.eq_nil_of_infix_nil
                simpa [hrest_nil] using hsub_rest
              exact False.elim (if_neg this)
          | inr hf =>
              simpa [hfi] using hf


prove_correct isSublist by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 sub main if_pos)
  exact (goal_1 sub main found rest invariant_rest_infix_of_main if_pos_1)
  exact (goal_2 sub main found rest invariant_rest_infix_of_main invariant_not_missed a if_pos if_neg_1)
  exact (goal_3 sub main found rest invariant_not_missed if_neg_1)
  exact (goal_4 sub main found rest invariant_rest_infix_of_main invariant_not_missed a if_neg_1)
  exact (goal_5 sub main if_neg found rest invariant_found_sound invariant_not_missed done_1 i rest_1 i_1)
end Proof
