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
    verina_basic_33: Return the smallest natural number missing from a sorted list of natural numbers.

    Natural language breakdown:
    1. The input is a list s : List Nat.
    2. The input list is assumed to be sorted in non-decreasing order.
    3. The result r : Nat is the smallest natural number (starting from 0) that does not appear in s.
    4. Therefore, r is not a member of s.
    5. Every natural number m smaller than r must appear in s.
    6. These two properties uniquely determine r because Nat is well-ordered.
-/

section Specs
-- Helper: predicate that a number is missing from the list
-- Using standard membership notation (List.instMembership).
def MissingFrom (s : List Nat) (n : Nat) : Prop := n ∉ s

-- Precondition: input list is sorted in non-decreasing order.
def precondition (s : List Nat) : Prop :=
  s.Sorted (· ≤ ·)

-- Postcondition: result is the least natural number not in s.
-- Characterization:
-- (1) result is missing from s
-- (2) every smaller number is present in s
def postcondition (s : List Nat) (result : Nat) : Prop :=
  MissingFrom s result ∧
  (∀ m : Nat, m < result → m ∈ s)
end Specs

section Impl
method smallestMissingNumber (s : List Nat)
  return (result : Nat)
  require precondition s
  ensures postcondition s result
  do
  let mut cand : Nat := 0
  let mut cur := s
  let mut done : Bool := false

  while (!done)
    -- cand stays aligned with how many initial naturals we have confirmed to be in s
    -- Initialization: cand = 0 so ∀ m < 0 is trivial.
    -- Preservation: when cand increments, we have seen x = cand, so all m < cand+1 are in s.
    -- Sufficiency: on exit we will have cand ∉ s (shown below) and all m < cand are in s.
    invariant "inv_prefix_present" (∀ m : Nat, m < cand → m ∈ s)
    -- We never remove elements from s; cur is always some suffix of s.
    -- This helps relate decisions about head x to membership in the original list s.
    invariant "inv_cur_suffix" (∃ t : List Nat, s = t ++ cur)
    -- While looping, cand has not been found in the already-consumed prefix.
    -- Preservation: when dropping x < cand, sortedness implies x ≠ cand.
    -- When consuming x = cand we increment cand, restoring the property for the new cand.
    invariant "inv_cand_not_in_prefix" (∃ t : List Nat, s = t ++ cur ∧ cand ∉ t)
    -- If the loop terminates (done = true), then cand is missing from s.
    -- Cases: cur = [] => cand ∉ s; or head x > cand with sortedness => cand cannot appear later.
    invariant "inv_done_implies_missing" (done = true → cand ∉ s)
    done_with done = true
  do
    match cur with
    | [] =>
      done := true
    | x :: xs =>
      if x < cand then
        cur := xs
      else
        if x = cand then
          cand := cand + 1
          cur := xs
        else
          -- x > cand, since x is the first element >= cand in a sorted list
          done := true

  return cand
end Impl

section TestCases
-- Test case 1: example from prompt
-- s = [0, 1, 2, 6, 9] => smallest missing is 3
def test1_s : List Nat := [0, 1, 2, 6, 9]
def test1_Expected : Nat := 3

-- Test case 2: list starts above 0 => missing is 0
def test2_s : List Nat := [4, 5, 10, 11]
def test2_Expected : Nat := 0

-- Test case 3: complete prefix from 0 to 5 => missing is 6
def test3_s : List Nat := [0, 1, 2, 3, 4, 5]
def test3_Expected : Nat := 6

-- Test case 4: empty list => missing is 0
def test4_s : List Nat := []
def test4_Expected : Nat := 0

-- Test case 5: gap at 1
def test5_s : List Nat := [0, 2, 3, 4]
def test5_Expected : Nat := 1

-- Test case 6: single element [0] => missing is 1
def test6_s : List Nat := [0]
def test6_Expected : Nat := 1

-- Test case 7: duplicates allowed, still least missing
def test7_s : List Nat := [0, 0, 1, 1, 3]
def test7_Expected : Nat := 2

-- Test case 8: long initial gap (no 0)
def test8_s : List Nat := [2, 2, 2]
def test8_Expected : Nat := 0

-- Test case 9: missing in middle with duplicates
def test9_s : List Nat := [0, 1, 1, 2, 4, 4]
def test9_Expected : Nat := 3

-- Recommend to validate: 1, 3, 7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((smallestMissingNumber test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((smallestMissingNumber test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((smallestMissingNumber test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((smallestMissingNumber test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((smallestMissingNumber test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((smallestMissingNumber test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((smallestMissingNumber test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((smallestMissingNumber test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((smallestMissingNumber test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for smallestMissingNumber
prove_precondition_decidable_for smallestMissingNumber
prove_postcondition_decidable_for smallestMissingNumber
derive_tester_for smallestMissingNumber
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (List Nat)
    let res := smallestMissingNumberTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct smallestMissingNumber by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_cand_not_in_prefix : ∃ t, s = t ++ cur ∧ cand ∉ t)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_pos_1 : i < cand)
    (if_pos : done = false)
    : ∃ t, s = t ++ i_1 := by
    rcases invariant_inv_cur_suffix with ⟨t0, ht0⟩
    refine ⟨t0 ++ [i], ?_⟩
    -- rewrite the known suffix fact using `cur = i :: i_1`, then reassociate
    calc
      s = t0 ++ cur := ht0
      _ = t0 ++ (i :: i_1) := by simpa [i_2]
      _ = t0 ++ ([i] ++ i_1) := by simp
      _ = (t0 ++ [i]) ++ i_1 := by
            simp [List.append_assoc]

theorem goal_1
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_cand_not_in_prefix : ∃ t, s = t ++ cur ∧ cand ∉ t)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_pos_1 : i < cand)
    (if_pos : done = false)
    : ∃ t, s = t ++ i_1 ∧ cand ∉ t := by
  rcases invariant_inv_cand_not_in_prefix with ⟨t1, hs, hnot⟩
  refine ⟨t1 ++ [i], ?_, ?_⟩
  · -- show s = (t1 ++ [i]) ++ i_1
    have hs' : s = t1 ++ (i :: i_1) := by
      simpa [i_2] using hs
    -- use append_cons to rewrite and then reassociate
    calc
      s = t1 ++ (i :: i_1) := hs'
      _ = t1 ++ [i] ++ i_1 := by
        simpa using (List.append_cons t1 i i_1).symm
      _ = (t1 ++ [i]) ++ i_1 := by
        simp [List.append_assoc]
  · -- show cand ∉ t1 ++ [i]
    intro hmem
    have : cand ∈ t1 ∨ cand ∈ [i] := (List.mem_append).1 hmem
    cases this with
    | inl h =>
        exact hnot h
    | inr h =>
        have hcand_eq : cand = i := (List.mem_singleton).1 h
        have : i ≠ cand := ne_of_lt if_pos_1
        exact this (hcand_eq.symm)

theorem goal_2
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_cand_not_in_prefix : ∃ t, s = t ++ cur ∧ cand ∉ t)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_pos_1 : i = cand)
    (if_pos : done = false)
    (if_neg : cand ≤ i)
    : ∃ t, s = t ++ i_1 := by
    rcases invariant_inv_cur_suffix with ⟨t0, hs⟩
    refine ⟨t0 ++ [i], ?_⟩
    -- use `List.append_cons` directly to avoid simp recursion issues
    calc
      s = t0 ++ cur := hs
      _ = t0 ++ (i :: i_1) := by simpa [i_2]
      _ = (t0 ++ [i]) ++ i_1 := by
            simpa [List.append_assoc] using (List.append_cons t0 i i_1).symm

theorem goal_3_0
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_pos_1 : i = cand)
    (if_pos : done = false)
    (if_neg : cand ≤ i)
    (t1 : List ℕ)
    (hs : s = t1 ++ cur)
    (hnot_cand_t1 : cand ∉ t1)
    : s = t1 ++ i :: i_1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_3_1
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_pos_1 : i = cand)
    (if_pos : done = false)
    (if_neg : cand ≤ i)
    (t1 : List ℕ)
    (hs : s = t1 ++ cur)
    (hnot_cand_t1 : cand ∉ t1)
    (hs' : s = t1 ++ i :: i_1)
    (hmem_t1 : cand + 1 ∈ t1)
    (hs_sorted : List.Sorted (fun x1 x2 ↦ x1 ≤ x2) s)
    (hmem_succ : cand + 1 ∈ t1 ∨ cand + 1 = i)
    : ∀ x ∈ t1, x ≤ i := by
    have hs_sorted' : List.Sorted (fun x1 x2 ↦ x1 ≤ x2) (t1 ++ i :: i_1) := by
      simpa [hs'] using hs_sorted

    -- General lemma: if (l ++ i :: r) is sorted, then every element of l is ≤ i.
    have hprefix_le :
        ∀ (l r : List ℕ),
          List.Sorted (fun x1 x2 ↦ x1 ≤ x2) (l ++ i :: r) →
            ∀ x ∈ l, x ≤ i := by
      intro l r hsorted
      induction l with
      | nil =>
          intro x hx
          simpa using hx
      | cons a t ih =>
          -- (a :: t) ++ i :: r = a :: (t ++ i :: r)
          have hsorted_cons :
              List.Sorted (fun x1 x2 ↦ x1 ≤ x2) (a :: (t ++ i :: r)) := by
            simpa [List.cons_append] using hsorted
          cases hsorted_cons with
          | cons hrel htail =>
              have ha_le_i : a ≤ i := by
                apply hrel i
                simp
              intro x hx
              have hx' : x = a ∨ x ∈ t := by
                simpa using hx
              cases hx' with
              | inl hxa =>
                  simpa [hxa] using ha_le_i
              | inr hx_t =>
                  have hsorted_tail :
                      List.Sorted (fun x1 x2 ↦ x1 ≤ x2) (t ++ i :: r) := by
                    simpa using htail
                  exact ih hsorted_tail x hx_t

    exact hprefix_le t1 i_1 hs_sorted'

theorem goal_3_2
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_pos_1 : i = cand)
    (if_pos : done = false)
    (if_neg : cand ≤ i)
    (t1 : List ℕ)
    (hs : s = t1 ++ cur)
    (hnot_cand_t1 : cand ∉ t1)
    (hs' : s = t1 ++ i :: i_1)
    (hmem_t1 : cand + 1 ∈ t1)
    (hs_sorted : List.Sorted (fun x1 x2 ↦ x1 ≤ x2) s)
    (ht1_le_i : ∀ x ∈ t1, x ≤ i)
    (ht1_le_cand : ∀ x ∈ t1, x ≤ cand)
    (hmem_succ : cand + 1 ∈ t1 ∨ cand + 1 = i)
    : cand + 1 ∉ t1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_3_3
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_pos_1 : i = cand)
    (if_pos : done = false)
    (if_neg : cand ≤ i)
    (t1 : List ℕ)
    (hs : s = t1 ++ cur)
    (hnot_cand_t1 : cand ∉ t1)
    (hs' : s = t1 ++ i :: i_1)
    (hsucc_eq_i : cand + 1 = i)
    (hmem_succ : cand + 1 ∈ t1 ∨ cand + 1 = i)
    (hmem_single : cand + 1 = i)
    : False := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_3
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_cand_not_in_prefix : ∃ t, s = t ++ cur ∧ cand ∉ t)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_pos_1 : i = cand)
    (if_pos : done = false)
    (if_neg : cand ≤ i)
    : ∃ t, s = t ++ i_1 ∧ cand + 1 ∉ t := by
    -- 2. extract the decomposition and the "cand not in prefix" fact
    rcases invariant_inv_cand_not_in_prefix with ⟨t1, hs, hnot_cand_t1⟩

    -- 3. rewrite the decomposition using cur = i :: i_1
    have hs' : s = t1 ++ (i :: i_1) := by
      (try simp at *; expose_names); exact (goal_3_0 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_done_implies_missing i i_1 i_2 if_pos_1 if_pos if_neg t1 hs hnot_cand_t1); done

    -- 4. choose the output prefix t := t1 ++ [i]
    refine ⟨t1 ++ [i], ?_, ?_⟩

    -- 5. prove s = (t1 ++ [i]) ++ i_1
    have hs'' : s = (t1 ++ [i]) ++ i_1 := by
      (try simp at *; expose_names); exact hs'; done
    · exact hs''

    -- 6. show cand + 1 ∉ t1 ++ [i] by contradiction and splitting membership over append
    intro hmem_succ
    have hmem_split : (cand + 1 ∈ t1) ∨ (cand + 1 ∈ [i]) := by
      (try simp at *; expose_names); exact hmem_succ; done
    cases hmem_split with
    | inl hmem_t1 =>
        -- 8/9. use sortedness + split at i=cand to show elements of t1 are ≤ cand, hence cand+1 not in t1
        have hs_sorted : s.Sorted (· ≤ ·) := by
          -- precondition s is exactly sortedness
          (try simp at *; expose_names); exact require_1; done
        have ht1_le_i : ∀ x ∈ t1, x ≤ i := by
          -- standard "sorted append into cons" lemma: prefix elements ≤ head of suffix
          (try simp at *; expose_names); exact (goal_3_1 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_done_implies_missing i i_1 i_2 if_pos_1 if_pos if_neg t1 hs hnot_cand_t1 hs' hmem_t1 hs_sorted hmem_succ); done
        have ht1_le_cand : ∀ x ∈ t1, x ≤ cand := by
          (try simp at *; expose_names); exact fun x a ↦ le_of_le_of_eq (ht1_le_i x a) if_pos_1; done
        have hsucc_not_mem_t1 : cand + 1 ∉ t1 := by
          (try simp at *; expose_names); exact (goal_3_2 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_done_implies_missing i i_1 i_2 if_pos_1 if_pos if_neg t1 hs hnot_cand_t1 hs' hmem_t1 hs_sorted ht1_le_i ht1_le_cand hmem_succ); done
        exact (hsucc_not_mem_t1 hmem_t1).elim
    | inr hmem_single =>
        -- 7. reduce singleton membership to equality, then contradict cand+1 = cand
        have hsucc_eq_i : cand + 1 = i := by
          (try simp at *; expose_names); exact hmem_single; done
        have hsucc_eq_cand : cand + 1 = cand := by
          (try simp at *; expose_names); exact (goal_3_3 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_done_implies_missing i i_1 i_2 if_pos_1 if_pos if_neg t1 hs hnot_cand_t1 hs' hsucc_eq_i hmem_succ hmem_single); done
        have : (cand + 1) ≠ cand := by
          (try simp at *; expose_names); exact Ne.symm (Nat.ne_add_one cand); done
        exact (this hsucc_eq_cand).elim

theorem goal_4_0_1
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_neg_1 : ¬i = cand)
    (if_pos : done = false)
    (if_neg : cand ≤ i)
    (t : List ℕ)
    (hs : s = t ++ cur)
    (hnot_t : cand ∉ t)
    (hs_sorted : List.Sorted (fun x1 x2 ↦ x1 ≤ x2) s)
    (hs_cons : s = t ++ i :: i_1)
    (hcand_lt_i : cand < i)
    (hs_sorted_cons : List.Sorted (fun x1 x2 ↦ x1 ≤ x2) (t ++ i :: i_1))
    (x : ℕ)
    (hx : x ∈ i_1)
    (hs_sorted_suffix : (∀ b ∈ i_1, i ≤ b) ∧ List.Sorted (fun x1 x2 ↦ x1 ≤ x2) i_1)
    : ∀ y ∈ i_1, i ≤ y := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_4_0_0
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_neg_1 : ¬i = cand)
    (if_pos : done = false)
    (if_neg : cand ≤ i)
    (t : List ℕ)
    (hs : s = t ++ cur)
    (hnot_t : cand ∉ t)
    (hs_sorted : List.Sorted (fun x1 x2 ↦ x1 ≤ x2) s)
    (hs_cons : s = t ++ i :: i_1)
    (hcand_lt_i : cand < i)
    (hs_sorted_cons : List.Sorted (fun x1 x2 ↦ x1 ≤ x2) (t ++ i :: i_1))
    (x : ℕ)
    (hx : x ∈ i_1)
    : (∀ b ∈ i_1, i ≤ b) ∧ List.Sorted (fun x1 x2 ↦ x1 ≤ x2) i_1 := by
    sorry

theorem goal_4_0
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_neg_1 : ¬i = cand)
    (if_pos : done = false)
    (if_neg : cand ≤ i)
    (t : List ℕ)
    (hs : s = t ++ cur)
    (hnot_t : cand ∉ t)
    (hs_sorted : List.Sorted (fun x1 x2 ↦ x1 ≤ x2) s)
    (hs_cons : s = t ++ i :: i_1)
    (hcand_lt_i : cand < i)
    (hs_sorted_cons : List.Sorted (fun x1 x2 ↦ x1 ≤ x2) (t ++ i :: i_1))
    : ∀ x ∈ i_1, i ≤ x := by
    intro x hx

    have hs_sorted_suffix : List.Sorted (fun x1 x2 ↦ x1 ≤ x2) (i :: i_1) := by
      -- sortedness is preserved by dropping a prefix; drop (t.length) from (t ++ i :: i_1)
      -- and use `List.drop_left` computation to identify the result with (i :: i_1)
      (try simp at *; expose_names); exact (goal_4_0_0 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_done_implies_missing i i_1 i_2 if_neg_1 if_pos if_neg t hs hnot_t hs_sorted hs_cons hcand_lt_i hs_sorted_cons x hx); done

    have hhead_le_all_tail : ∀ y ∈ i_1, i ≤ y := by
      -- standard fact: if Sorted (≤) (i :: i_1) then head ≤ every element of tail
      -- prove by induction on i_1, using the cons characterization of Sorted
      (try simp at *; expose_names); exact (goal_4_0_1 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_done_implies_missing i i_1 i_2 if_neg_1 if_pos if_neg t hs hnot_t hs_sorted hs_cons hcand_lt_i hs_sorted_cons x hx hs_sorted_suffix); done

    exact hhead_le_all_tail x hx

theorem goal_4
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_cand_not_in_prefix : ∃ t, s = t ++ cur ∧ cand ∉ t)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (i : ℕ)
    (i_1 : List ℕ)
    (i_2 : cur = i :: i_1)
    (if_neg_1 : ¬i = cand)
    (if_pos : done = false)
    (if_neg : cand ≤ i)
    : cand ∉ s := by
    -- pick the prefix t such that s = t ++ cur and cand ∉ t
    rcases invariant_inv_cand_not_in_prefix with ⟨t, hs, hnot_t⟩

    -- use precondition as sortedness of s
    have hs_sorted : s.Sorted (· ≤ ·) := by
      simpa [precondition] using require_1

    -- rewrite the decomposition using cur = i :: i_1
    have hs_cons : s = t ++ (i :: i_1) := by
      simpa [i_2] using hs

    -- from cand ≤ i and i ≠ cand, derive cand < i
    have hcand_lt_i : cand < i := by
      have hne : cand ≠ i := by
        exact Ne.symm if_neg_1
      exact lt_of_le_of_ne if_neg hne

    -- sortedness transports to the specific shape t ++ (i :: i_1)
    have hs_sorted_cons : (t ++ (i :: i_1)).Sorted (· ≤ ·) := by
      simpa [hs_cons] using hs_sorted

    -- key local property from sortedness: every x in i_1 satisfies i ≤ x
    have hi_le_of_mem_tail : ∀ x ∈ i_1, i ≤ x := by
      (try simp at *; expose_names); exact (goal_4_0 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_done_implies_missing i i_1 i_2 if_neg_1 if_pos if_neg t hs hnot_t hs_sorted hs_cons hcand_lt_i hs_sorted_cons); done

    -- therefore cand cannot appear in the tail i_1 (since cand < i ≤ x would contradict x = cand)
    have hcand_not_mem_i1 : cand ∉ i_1 := by
      intro hmem
      have hi_le_cand : i ≤ cand := by
        have : i ≤ cand := hi_le_of_mem_tail cand hmem
        simpa using this
      exact (Nat.lt_le_asymm hcand_lt_i hi_le_cand).elim

    -- cand is not the head i (by branch condition) and not in the tail, so not in cur
    have hcand_not_mem_cur : cand ∉ cur := by
      -- rewrite cur, then use mem_cons
      intro hmem
      have hmem' : cand ∈ i :: i_1 := by
        simpa [i_2] using hmem
      have hsplit : cand = i ∨ cand ∈ i_1 := by
        simpa [List.mem_cons] using hmem'
      cases hsplit with
      | inl h_eq =>
          exact if_neg_1 h_eq.symm
      | inr h_tail =>
          exact hcand_not_mem_i1 h_tail

    -- combine not-in-prefix and not-in-suffix to conclude not-in-append, hence not in s
    have hcand_not_mem_append : cand ∉ t ++ cur := by
      exact List.not_mem_append hnot_t hcand_not_mem_cur

    -- finish using s = t ++ cur
    simpa [hs] using hcand_not_mem_append

theorem goal_5
    (s : List ℕ)
    (require_1 : precondition s)
    : ∃ t, s = t ++ s := by
    refine ⟨[], ?_⟩
    simp

theorem goal_6
    (s : List ℕ)
    (require_1 : precondition s)
    : ∃ t, s = t ++ s ∧ 0 ∉ t := by
    refine ⟨[], ?_, ?_⟩
    · simp
    · simp

theorem goal_7
    (s : List ℕ)
    (require_1 : precondition s)
    (cand : ℕ)
    (cur : List ℕ)
    (done : Bool)
    (invariant_inv_prefix_present : ∀ m < cand, m ∈ s)
    (invariant_inv_cur_suffix : ∃ t, s = t ++ cur)
    (invariant_inv_cand_not_in_prefix : ∃ t, s = t ++ cur ∧ cand ∉ t)
    (invariant_inv_done_implies_missing : done = true → cand ∉ s)
    (done_1 : done = true)
    (i : ℕ)
    (i_1 : List ℕ)
    (done_2 : Bool)
    (i_2 : cand = i ∧ cur = i_1 ∧ done = done_2)
    : postcondition s i := by
    rcases i_2 with ⟨hcand, hcur, hdone⟩
    unfold postcondition MissingFrom
    constructor
    · have : cand ∉ s := invariant_inv_done_implies_missing done_1
      simpa [hcand] using this
    · intro m hm
      have hm' : m < cand := by simpa [hcand] using hm
      exact invariant_inv_prefix_present m hm'

prove_correct smallestMissingNumber by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_cand_not_in_prefix invariant_inv_done_implies_missing i i_1 i_2 if_pos_1 if_pos)
  exact (goal_1 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_cand_not_in_prefix invariant_inv_done_implies_missing i i_1 i_2 if_pos_1 if_pos)
  exact (goal_2 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_cand_not_in_prefix invariant_inv_done_implies_missing i i_1 i_2 if_pos_1 if_pos if_neg)
  exact (goal_3 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_cand_not_in_prefix invariant_inv_done_implies_missing i i_1 i_2 if_pos_1 if_pos if_neg)
  exact (goal_4 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_cand_not_in_prefix invariant_inv_done_implies_missing i i_1 i_2 if_neg_1 if_pos if_neg)
  exact (goal_5 s require_1)
  exact (goal_6 s require_1)
  exact (goal_7 s require_1 cand cur done invariant_inv_prefix_present invariant_inv_cur_suffix invariant_inv_cand_not_in_prefix invariant_inv_done_implies_missing done_1 i i_1 done_2 i_2)
end Proof
