import CaseStudies.Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findMajorityElement: Find the majority element in a list of integers
    Natural language breakdown:
    1. We are given a list of integers (may include duplicates and negative numbers)
    2. A majority element is defined as an element that appears strictly more than half the number of times in the list
    3. Formally, element x is a majority element if lst.count x > lst.length / 2
    4. If such a majority element exists, return that element
    5. If no majority element exists, return -1
    6. Edge case: Empty list has no majority element, return -1
    7. Note: There can be at most one majority element in any list (since it must appear more than half the time)
    8. The result is either the unique majority element or -1
-/

section Specs
-- Helper function to check if an element is a majority element
def isMajorityElement (lst : List Int) (x : Int) : Prop :=
  lst.count x > lst.length / 2

-- Helper function to check if a majority element exists
def hasMajorityElement (lst : List Int) : Prop :=
  ∃ x, x ∈ lst ∧ isMajorityElement lst x

-- Precondition: no restrictions on input
def precondition (lst : List Int) : Prop :=
  True

-- Postcondition: result is either the majority element or -1
def postcondition (lst : List Int) (result : Int) : Prop :=
  (hasMajorityElement lst → (result ∈ lst ∧ isMajorityElement lst result)) ∧
  (¬hasMajorityElement lst → result = -1)
end Specs

section Impl
method findMajorityElement (lst : List Int)
  return (result : Int)
  require precondition lst
  ensures postcondition lst result
  do
  let n := lst.length
  let threshold := n / 2
  let mut i := 0
  let mut found := false
  let mut candidate : Int := -1

  while i < n
    -- i is bounded by list length
    invariant "i_bounds" 0 ≤ i ∧ i ≤ n
    -- found implies candidate is a majority element in the list
    invariant "found_implies_majority" found = true → (candidate ∈ lst ∧ isMajorityElement lst candidate)
    -- not found implies no majority element among first i elements
    invariant "not_found_checked" found = false → (∀ k : Nat, k < i → ¬isMajorityElement lst (lst.get! k))
    done_with i >= n
  do
    let elem := lst.get! i
    let mut count := 0
    let mut j := 0

    -- Count occurrences of elem in lst
    while j < n
      -- j is bounded by list length
      invariant "j_bounds" 0 ≤ j ∧ j ≤ n
      -- count equals occurrences of elem in lst[0..j]
      invariant "count_correct" count = (lst.take j).count elem
      -- preserve outer loop invariants
      invariant "found_preserved" found = true → (candidate ∈ lst ∧ isMajorityElement lst candidate)
      invariant "i_preserved" 0 ≤ i ∧ i < n
      invariant "elem_in_list" i < lst.length → elem = lst.get! i
      invariant "not_found_checked_inner" found = false → (∀ k : Nat, k < i → ¬isMajorityElement lst (lst.get! k))
      done_with j >= n
    do
      if lst.get! j = elem then
        count := count + 1
      j := j + 1

    -- Check if this element is a majority
    if count > threshold then
      found := true
      candidate := elem

    i := i + 1

  if found then
    return candidate
  else
    return -1
end Impl

section Proof
set_option maxHeartbeats 10000000

attribute [grind] List.take_succ_eq_append_getElem List.getElem?_eq_getElem

-- prove_correct findMajorityElement by
  -- loom_solve_async <;> (try simp at *; expose_names)

theorem goal_0
    (lst : List ℤ)
    (require_1 : precondition lst)
    (candidate : ℤ)
    (found : Bool)
    (i : ℕ)
    (a_1 : i ≤ lst.length)
    (invariant_found_implies_majority : found = true → candidate ∈ lst ∧ isMajorityElement lst candidate)
    (if_pos : i < lst.length)
    (count : ℕ)
    (j : ℕ)
    (a_3 : j ≤ lst.length)
    (invariant_found_preserved : found = true → candidate ∈ lst ∧ isMajorityElement lst candidate)
    (a_5 : i < lst.length)
    (if_pos_1 : j < lst.length)
    (a : True)
    (invariant_not_found_checked : found = false → ∀ k < i, ¬isMajorityElement lst (lst[k]?.getD 0))
    (a_2 : True)
    (invariant_count_correct : count = List.count (lst[i]?.getD 0) (List.take j lst))
    (a_4 : True)
    (invariant_not_found_checked_inner : found = false → ∀ k < i, ¬isMajorityElement lst (lst[k]?.getD 0))
    (if_pos_2 : lst[j]?.getD 0 = lst[i]?.getD 0)
    : count + 1 = List.count (lst[i]?.getD 0) (List.take (j + 1) lst) := by
    rw [List.take_succ_eq_append_getElem if_pos_1]
    rw [List.count_append]
    rw [← invariant_count_correct]
    simp only [List.count_singleton]
    have h_eq : lst[j] = lst[j]?.getD 0 := by
      simp only [List.getElem?_eq_getElem if_pos_1, Option.getD_some]
    rw [h_eq, if_pos_2]
    simp only [beq_self_eq_true, ↓reduceIte]

theorem goal_1
    (lst : List ℤ)
    (require_1 : precondition lst)
    (candidate : ℤ)
    (found : Bool)
    (i : ℕ)
    (a_1 : i ≤ lst.length)
    (invariant_found_implies_majority : found = true → candidate ∈ lst ∧ isMajorityElement lst candidate)
    (if_pos : i < lst.length)
    (count : ℕ)
    (j : ℕ)
    (a_3 : j ≤ lst.length)
    (invariant_found_preserved : found = true → candidate ∈ lst ∧ isMajorityElement lst candidate)
    (a_5 : i < lst.length)
    (if_pos_1 : j < lst.length)
    (a : True)
    (invariant_not_found_checked : found = false → ∀ k < i, ¬isMajorityElement lst (lst[k]?.getD 0))
    (a_2 : True)
    (invariant_count_correct : count = List.count (lst[i]?.getD 0) (List.take j lst))
    (a_4 : True)
    (invariant_not_found_checked_inner : found = false → ∀ k < i, ¬isMajorityElement lst (lst[k]?.getD 0))
    (if_neg : ¬lst[j]?.getD 0 = lst[i]?.getD 0)
    : count = List.count (lst[i]?.getD 0) (List.take (j + 1) lst) := by
    rw [List.take_succ]
    have h_some : lst[j]? = some lst[j] := List.getElem?_eq_some_iff.mpr ⟨if_pos_1, rfl⟩
    rw [h_some]
    simp only [Option.toList]
    rw [List.count_append]
    rw [List.count_singleton]
    have h_getD : lst[j]?.getD 0 = lst[j] := by simp [h_some]
    have h_ne : lst[j] ≠ lst[i]?.getD 0 := by
      intro h_eq
      apply if_neg
      rw [h_getD, h_eq]
    simp only [beq_iff_eq, h_ne, ↓reduceIte, add_zero]
    exact invariant_count_correct

theorem goal_2
    (lst : List ℤ)
    (require_1 : precondition lst)
    (candidate : ℤ)
    (found : Bool)
    (i : ℕ)
    (a_1 : i ≤ lst.length)
    (invariant_found_implies_majority : found = true → candidate ∈ lst ∧ isMajorityElement lst candidate)
    (if_pos : i < lst.length)
    (count : ℕ)
    (j : ℕ)
    (a_3 : j ≤ lst.length)
    (invariant_found_preserved : found = true → candidate ∈ lst ∧ isMajorityElement lst candidate)
    (a_5 : i < lst.length)
    (i_1 : ℕ)
    (j_1 : ℕ)
    (a : True)
    (invariant_not_found_checked : found = false → ∀ k < i, ¬isMajorityElement lst (lst[k]?.getD 0))
    (a_2 : True)
    (invariant_count_correct : count = List.count (lst[i]?.getD 0) (List.take j lst))
    (a_4 : True)
    (invariant_not_found_checked_inner : found = false → ∀ k < i, ¬isMajorityElement lst (lst[k]?.getD 0))
    (done_2 : lst.length ≤ j)
    (i_2 : count = i_1 ∧ j = j_1)
    (if_pos_1 : lst.length / 2 < i_1)
    : lst[i]?.getD 0 ∈ lst ∧ isMajorityElement lst (lst[i]?.getD 0) := by
    have h_count_eq_i1 : count = i_1 := i_2.1
    have h_majority_count : lst.length / 2 < count := by omega
    have h_take_eq_lst : List.take j lst = lst := List.take_of_length_le done_2
    have h_count_full : count = List.count (lst[i]?.getD 0) lst := by
      rw [invariant_count_correct, h_take_eq_lst]
    have h_getElem?_eq : lst[i]? = some lst[i] := List.getElem?_eq_getElem if_pos
    have h_getD_eq : lst[i]?.getD 0 = lst[i] := by simp [h_getElem?_eq, Option.getD_some]
    constructor
    · rw [h_getD_eq]
      exact List.getElem_mem if_pos
    · unfold isMajorityElement
      rw [h_count_full] at h_majority_count
      omega

theorem goal_3
    (lst : List ℤ)
    (require_1 : precondition lst)
    (candidate : ℤ)
    (found : Bool)
    (i : ℕ)
    (a_1 : i ≤ lst.length)
    (invariant_found_implies_majority : found = true → candidate ∈ lst ∧ isMajorityElement lst candidate)
    (if_pos : i < lst.length)
    (count : ℕ)
    (j : ℕ)
    (a_3 : j ≤ lst.length)
    (invariant_found_preserved : found = true → candidate ∈ lst ∧ isMajorityElement lst candidate)
    (a_5 : i < lst.length)
    (i_1 : ℕ)
    (j_1 : ℕ)
    (a : True)
    (invariant_not_found_checked : found = false → ∀ k < i, ¬isMajorityElement lst (lst[k]?.getD 0))
    (a_2 : True)
    (invariant_count_correct : count = List.count (lst[i]?.getD 0) (List.take j lst))
    (a_4 : True)
    (invariant_not_found_checked_inner : found = false → ∀ k < i, ¬isMajorityElement lst (lst[k]?.getD 0))
    (done_2 : lst.length ≤ j)
    (i_2 : count = i_1 ∧ j = j_1)
    (if_neg : i_1 ≤ lst.length / 2)
    : found = false → ∀ k < i + 1, ¬isMajorityElement lst (lst[k]?.getD 0) := by
    intro hfound k hk
    -- Split k < i + 1 into k < i or k = i
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · -- Case k < i: use the invariant
      exact invariant_not_found_checked hfound k hlt
    · -- Case k = i: need to show lst[i]?.getD 0 is not a majority element
      subst heq
      unfold isMajorityElement
      -- We need to show ¬(lst.count (lst[i]?.getD 0) > lst.length / 2)
      -- From invariant_count_correct and done_2, count = List.count (lst[i]?.getD 0) lst
      have htake : List.take j lst = lst := List.take_of_length_le done_2
      rw [htake] at invariant_count_correct
      -- Now count = List.count (lst[i]?.getD 0) lst
      -- From i_2, count = i_1
      -- From if_neg, i_1 ≤ lst.length / 2
      have hcount_eq : count = i_1 := i_2.1
      rw [← invariant_count_correct, hcount_eq]
      omega

theorem goal_4
    (lst : List ℤ)
    (require_1 : precondition lst)
    (candidate : ℤ)
    (found : Bool)
    (i : ℕ)
    (a_1 : i ≤ lst.length)
    (invariant_found_implies_majority : found = true → candidate ∈ lst ∧ isMajorityElement lst candidate)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (if_pos : i_2 = true)
    (a : True)
    (invariant_not_found_checked : found = false → ∀ k < i, ¬isMajorityElement lst (lst[k]?.getD 0))
    (done_1 : lst.length ≤ i)
    (i_4 : candidate = i_1 ∧ found = i_2 ∧ i = i_3)
    : postcondition lst i_1 := by
    unfold postcondition
    -- Extract from i_4
    obtain ⟨h_cand, h_found, _⟩ := i_4
    -- found = true
    have found_true : found = true := by rw [h_found]; exact if_pos
    -- Get that candidate is a majority element
    have h_maj := invariant_found_implies_majority found_true
    -- candidate = i_1, so i_1 is a majority element
    rw [h_cand] at h_maj
    -- h_maj : i_1 ∈ lst ∧ isMajorityElement lst i_1
    constructor
    · -- hasMajorityElement lst → i_1 ∈ lst ∧ isMajorityElement lst i_1
      intro _
      exact h_maj
    · -- ¬hasMajorityElement lst → i_1 = -1
      intro h_no_maj
      -- But we have a majority element, contradiction
      exfalso
      apply h_no_maj
      unfold hasMajorityElement
      exact ⟨i_1, h_maj⟩

theorem goal_5
    (lst : List ℤ)
    (require_1 : precondition lst)
    (candidate : ℤ)
    (found : Bool)
    (i : ℕ)
    (a_1 : i ≤ lst.length)
    (invariant_found_implies_majority : found = true → candidate ∈ lst ∧ isMajorityElement lst candidate)
    (i_1 : ℤ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (a : True)
    (invariant_not_found_checked : found = false → ∀ k < i, ¬isMajorityElement lst (lst[k]?.getD 0))
    (done_1 : lst.length ≤ i)
    (i_4 : candidate = i_1 ∧ found = i_2 ∧ i = i_3)
    (if_neg : i_2 = false)
    : postcondition lst (-1) := by
  unfold postcondition
  constructor
  · -- hasMajorityElement lst → (-1 ∈ lst ∧ isMajorityElement lst (-1))
    intro hmaj
    unfold hasMajorityElement at hmaj
    obtain ⟨x, hx_mem, hx_maj⟩ := hmaj
    -- x ∈ lst means there exists an index k < lst.length with lst[k] = x
    rw [List.mem_iff_getElem] at hx_mem
    obtain ⟨k, hk_lt, hk_eq⟩ := hx_mem
    -- From the invariant, we know found = false implies no element at index < i is majority
    have hfound_false : found = false := by
      obtain ⟨_, hfi2, _⟩ := i_4
      rw [hfi2]
      exact if_neg
    have hinv := invariant_not_found_checked hfound_false
    -- k < lst.length ≤ i, so k < i
    have hk_lt_i : k < i := Nat.lt_of_lt_of_le hk_lt done_1
    have hnotmaj := hinv k hk_lt_i
    -- lst[k]?.getD 0 = lst[k] since k < lst.length
    have heq : lst[k]?.getD 0 = lst[k] := by
      rw [List.getElem?_eq_getElem hk_lt]
      simp [Option.getD_some]
    rw [heq] at hnotmaj
    -- But we have isMajorityElement lst x and lst[k] = x
    rw [← hk_eq] at hx_maj
    exact absurd hx_maj hnotmaj
  · -- ¬hasMajorityElement lst → -1 = -1
    intro _
    rfl


prove_correct findMajorityElement by
  loom_solve_async
end Proof
