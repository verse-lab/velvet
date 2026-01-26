import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    containsZ: Determine whether a given string contains the character 'z' or 'Z'.
    Natural language breakdown:
    1. Input is a string s.
    2. The method returns a Boolean.
    3. The result is true exactly when s contains at least one character equal to 'z' or equal to 'Z'.
    4. Otherwise the result is false.
    5. There are no preconditions.
-/

section Specs
-- Helper predicate: the string contains 'z' or 'Z'.
-- We state this via membership of the character list representation of the string.
def hasZ (s : String) : Prop :=
  ('z' ∈ s.toList) ∨ ('Z' ∈ s.toList)

-- No preconditions.
def precondition (s : String) : Prop :=
  True

-- Postcondition: result is true iff s contains 'z' or 'Z'.
def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ hasZ s) ∧
  (result = false ↔ ¬ hasZ s)
end Specs

section Impl
method containsZ (s : String) return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
    let chars := s.toList
    let mut rest := chars
    let mut found := false

    while (rest ≠ []) ∧ (found = false)
      -- Invariant 1: rest is always a suffix of the original character list.
      -- Init: rest = chars = [] ++ chars. Preserved: rest := cs keeps suffix property by extending the prefix.
      invariant "inv_rest_suffix"
        (∃ pref : List Char, chars = pref ++ rest)
      -- Invariant 2: if we have not found a 'z'/'Z' yet, then the already-processed prefix contains no 'z'/'Z'.
      -- Init: prefix = []. Preserved: when we pop c from rest without setting found, we learn c ≠ 'z' and c ≠ 'Z',
      -- and prefix extends by c, so the property remains true.
      invariant "inv_notfound_pref_noZ"
        (found = false → ∃ pref : List Char, chars = pref ++ rest ∧ ('z' ∉ pref) ∧ ('Z' ∉ pref))
      -- Invariant 3: once found becomes true, we have witnessed a 'z'/'Z' in the original list of chars.
      -- This avoids needing to relate String.toList to String.data explicitly.
      -- Init: found=false. Preserved: the only assignment to found=true happens when current c is 'z'/'Z',
      -- which implies membership in chars, hence in s.toList.
      invariant "inv_found_implies_hasZ_chars"
        (found = true → (('z' ∈ chars) ∨ ('Z' ∈ chars)))
    do
      match rest with
      | [] =>
        -- unreachable due to loop condition, but keeps match total
        rest := []
      | c :: cs =>
        if (c = 'z') ∨ (c = 'Z') then
          found := true
        rest := cs

    return found
end Impl

section Proof
set_option maxHeartbeats 10000000

-- prove_correct containsZ by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (s : String)
    (require_1 : precondition s)
    (found : Bool)
    (rest : List Char)
    (invariant_inv_rest_suffix : ∃ pref, s.data = pref ++ rest)
    (invariant_inv_notfound_pref_noZ : found = false → ∃ pref, s.data = pref ++ rest ∧ 'z' ∉ pref ∧ 'Z' ∉ pref)
    (invariant_inv_found_implies_hasZ_chars : found = true → 'z' ∈ s.data ∨ 'Z' ∈ s.data)
    (a : ¬rest = [])
    (a_1 : found = false)
    (i : Char)
    (i_1 : List Char)
    (i_2 : rest = i :: i_1)
    (if_pos : i = 'z' ∨ i = 'Z')
    : ∃ pref, s.data = pref ++ i_1 := by
    rcases invariant_inv_rest_suffix with ⟨pref0, hpref0⟩
    refine ⟨pref0 ++ [i], ?_⟩
    -- rewrite rest as i :: i_1, then reassociate/simplify appends
    simpa [hpref0, i_2, List.append_assoc] using (hpref0.trans (by simp [i_2, List.append_assoc]))

theorem goal_1
    (s : String)
    (require_1 : precondition s)
    (found : Bool)
    (rest : List Char)
    (invariant_inv_rest_suffix : ∃ pref, s.data = pref ++ rest)
    (invariant_inv_notfound_pref_noZ : found = false → ∃ pref, s.data = pref ++ rest ∧ 'z' ∉ pref ∧ 'Z' ∉ pref)
    (invariant_inv_found_implies_hasZ_chars : found = true → 'z' ∈ s.data ∨ 'Z' ∈ s.data)
    (a : ¬rest = [])
    (a_1 : found = false)
    (i : Char)
    (i_1 : List Char)
    (i_2 : rest = i :: i_1)
    (if_neg : ¬i = 'z' ∧ ¬i = 'Z')
    : ∃ pref, s.data = pref ++ i_1 := by
    rcases invariant_inv_rest_suffix with ⟨pref0, hpref0⟩
    refine ⟨pref0 ++ [i], ?_⟩
    -- rewrite `rest` as `i :: i_1` and reassociate appends
    calc
      s.data = pref0 ++ rest := hpref0
      _ = pref0 ++ (i :: i_1) := by simpa [i_2]
      _ = (pref0 ++ [i]) ++ i_1 := by
            simp [List.append_assoc]

theorem goal_2
    (s : String)
    (require_1 : precondition s)
    (found : Bool)
    (rest : List Char)
    (invariant_inv_rest_suffix : ∃ pref, s.data = pref ++ rest)
    (invariant_inv_notfound_pref_noZ : found = false → ∃ pref, s.data = pref ++ rest ∧ 'z' ∉ pref ∧ 'Z' ∉ pref)
    (invariant_inv_found_implies_hasZ_chars : found = true → 'z' ∈ s.data ∨ 'Z' ∈ s.data)
    (a : ¬rest = [])
    (a_1 : found = false)
    (i : Char)
    (i_1 : List Char)
    (i_2 : rest = i :: i_1)
    (if_neg : ¬i = 'z' ∧ ¬i = 'Z')
    : found = false → ∃ pref, s.data = pref ++ i_1 ∧ 'z' ∉ pref ∧ 'Z' ∉ pref := by
  intro hfound
  rcases invariant_inv_notfound_pref_noZ hfound with ⟨pref0, hs, hz0, hZ0⟩
  refine ⟨pref0 ++ [i], ?_, ?_, ?_⟩
  · -- s.data = (pref0 ++ [i]) ++ i_1
    calc
      s.data = pref0 ++ rest := hs
      _ = pref0 ++ (i :: i_1) := by simpa [i_2]
      _ = (pref0 ++ [i]) ++ i_1 := by
        simp [List.append_assoc]
  · -- 'z' ∉ pref0 ++ [i]
    apply List.not_mem_append hz0
    have : 'z' ≠ i := by
      intro hzEq
      exact if_neg.1 (hzEq.symm)
    -- now 'z' ∉ [i]
    simpa [List.mem_singleton] using this
  · -- 'Z' ∉ pref0 ++ [i]
    apply List.not_mem_append hZ0
    have : 'Z' ≠ i := by
      intro hZEq
      exact if_neg.2 (hZEq.symm)
    simpa [List.mem_singleton] using this

theorem goal_3
    (s : String)
    (require_1 : precondition s)
    : ∃ pref, s.toList = pref ++ s.toList := by
    refine ⟨([] : List Char), ?_⟩
    simp

theorem goal_4
    (s : String)
    (require_1 : precondition s)
    : ∃ pref, s.toList = pref ++ s.toList ∧ 'z' ∉ pref ∧ 'Z' ∉ pref := by
    refine ⟨([] : List Char), ?_⟩
    simp

theorem goal_5
    (s : String)
    (require_1 : precondition s)
    (found : Bool)
    (rest : List Char)
    (invariant_inv_rest_suffix : ∃ pref, s.data = pref ++ rest)
    (invariant_inv_notfound_pref_noZ : found = false → ∃ pref, s.data = pref ++ rest ∧ 'z' ∉ pref ∧ 'Z' ∉ pref)
    (invariant_inv_found_implies_hasZ_chars : found = true → 'z' ∈ s.data ∨ 'Z' ∈ s.data)
    (i : Bool)
    (rest_1 : List Char)
    (done_1 : ¬rest = [] → found = true)
    (i_1 : found = i ∧ rest = rest_1)
    : postcondition s i := by
    rcases i_1 with ⟨hfi, hrest⟩
    unfold postcondition
    constructor
    · -- (i = true ↔ hasZ s)
      constructor
      · intro hiT
        have hfoundT : found = true := by
          -- found = i and i = true
          simpa [hfi] using hiT
        have hz : ('z' ∈ s.data) ∨ ('Z' ∈ s.data) :=
          invariant_inv_found_implies_hasZ_chars hfoundT
        -- hasZ uses s.toList; s.toList is definitional equal to s.data
        simpa [hasZ] using hz
      · intro hhasZ
        -- prove i = true; split on i
        cases hi : i with
        | false =>
          exfalso
          have hfoundF : found = false := by
            -- from found = i and i = false
            simpa [hfi, hi]
          have hrestNil : rest = [] := by
            by_contra hne
            have hT : found = true := done_1 hne
            -- contradiction: found=false and found=true
            exact (by simpa [hfoundF] using hT)
          obtain ⟨pref, hsuff, hnz, hnZ⟩ := invariant_inv_notfound_pref_noZ hfoundF
          have hsdata : s.data = pref := by
            -- hsuff : s.data = pref ++ rest
            simpa [hrestNil] using hsuff
          have hzdata : ('z' ∈ s.data) ∨ ('Z' ∈ s.data) := by
            simpa [hasZ] using hhasZ
          have hzpref : ('z' ∈ pref) ∨ ('Z' ∈ pref) := by
            simpa [hsdata] using hzdata
          cases hzpref with
          | inl hz' => exact hnz hz'
          | inr hZ' => exact hnZ hZ'
        | true =>
          simpa [hi]
    · -- (i = false ↔ ¬ hasZ s)
      constructor
      · intro hiF
        intro hhasZ
        -- from i=false and hasZ, derive contradiction using first equivalence already proved above
        have hiT : i = true := by
          -- reuse the proved (i=true ↔ hasZ s) from the first conjunct
          have htrue : (i = true ↔ hasZ s) := by
            -- extract it from the first conjunct we already established
            -- (reprove locally in a lightweight way by using the already available assumptions)
            constructor
            · intro hiT
              have hfoundT : found = true := by simpa [hfi] using hiT
              have hz : ('z' ∈ s.data) ∨ ('Z' ∈ s.data) :=
                invariant_inv_found_implies_hasZ_chars hfoundT
              simpa [hasZ] using hz
            · intro hhasZ
              cases hi : i with
              | false =>
                exfalso
                have hfoundF : found = false := by simpa [hfi, hi]
                have hrestNil : rest = [] := by
                  by_contra hne
                  have hT : found = true := done_1 hne
                  exact (by simpa [hfoundF] using hT)
                obtain ⟨pref, hsuff, hnz, hnZ⟩ := invariant_inv_notfound_pref_noZ hfoundF
                have hsdata : s.data = pref := by
                  simpa [hrestNil] using hsuff
                have hzdata : ('z' ∈ s.data) ∨ ('Z' ∈ s.data) := by
                  simpa [hasZ] using hhasZ
                have hzpref : ('z' ∈ pref) ∨ ('Z' ∈ pref) := by
                  simpa [hsdata] using hzdata
                cases hzpref with
                | inl hz' => exact hnz hz'
                | inr hZ' => exact hnZ hZ'
              | true =>
                simpa [hi]
          exact (htrue.mpr hhasZ)
        -- contradiction between i=false and i=true
        exact (by simpa [hiF] using hiT)
      · intro hnot
        -- prove i = false by cases
        cases hi : i with
        | false =>
          rfl
        | true =>
          exfalso
          -- if i=true then hasZ, contradict ¬hasZ
          have hfoundT : found = true := by simpa [hfi, hi]
          have hz : ('z' ∈ s.data) ∨ ('Z' ∈ s.data) :=
            invariant_inv_found_implies_hasZ_chars hfoundT
          have : hasZ s := by simpa [hasZ] using hz
          exact hnot this

prove_correct containsZ by
  loom_solve <;> (try simp at *; expose_names)
  apply goal_0 <;> assumption
  apply goal_1 <;> assumption
  apply goal_2 <;> assumption
  apply goal_3 <;> assumption
  apply goal_4 <;> assumption
  apply goal_5 <;> assumption
end Proof
