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
  
end Specs

@[grind]
lemma lemma_2 [Inhabited α] (s : List α) (x : α) :
  (∀ i : Nat, i < s.length -> s[i]! ≠ x) -> ¬ x ∈ s := by
  sorry


section Impl
method containsZ (s : List Char) return (result : Bool)
  ensures (result ↔ ('z' ∈ s) ∨ ('Z' ∈ s))
  do
    let chars := s
    let mut found := false
    let mut i : Nat := 0

    while (i < chars.length) ∧ (found = false)
      invariant i <= chars.length
      invariant found <-> ∃ j : Nat, j < i ∧ (chars[j]! = 'z' ∨ chars[j]! = 'Z')
    do
      if (chars[i]! == 'z' || chars[i]! == 'Z') then
        found := true
      i := i + 1

    return found
end Impl

section Proof
set_option maxHeartbeats 10000000


prove_correct containsZ by
  loom_solve


end Proof
