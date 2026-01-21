import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000






def repeatsAt (l : List Char) (j : Nat) : Prop :=
  j < l.length ∧ ∃ i : Nat, i < j ∧ l[i]! = l[j]!



def noRepeatBefore (l : List Char) (j : Nat) : Prop :=
  ∀ k : Nat, k < j → ¬repeatsAt l k



def precondition (s : String) : Prop :=
  True





def postcondition (s : String) (result : Option Char) : Prop :=
  let l := s.toList
  (result = none ↔ (∀ j : Nat, ¬repeatsAt l j)) ∧
    (∀ c : Char,
      result = some c ↔
        (∃ j : Nat, repeatsAt l j ∧ noRepeatBefore l j ∧ l[j]! = c))


def test1_s : String := "abca"

def test1_Expected : Option Char := some 'a'

def test5_s : String := "abbc"

def test5_Expected : Option Char := some 'b'

def test9_s : String := "abcbad"

def test9_Expected : Option Char := some 'b'







section Proof
theorem test1_precondition : precondition test1_s := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition_0 : repeatsAt ['a', 'b', 'c', 'a'] 3 := by
  -- `hL` is irrelevant
  unfold repeatsAt
  constructor
  · decide
  · refine ⟨0, ?_, ?_⟩
    · decide
    · simp

theorem test1_postcondition_1 : ¬repeatsAt ['a', 'b', 'c', 'a'] 0 := by
    intro hRep0
    unfold repeatsAt at hRep0
    rcases hRep0 with ⟨_hLen, i, hiLt, _hEq⟩
    exact (Nat.not_lt_zero i) hiLt

theorem test1_postcondition_2 : ¬repeatsAt ['a', 'b', 'c', 'a'] 1 := by
  intro hRep1
  rcases hRep1 with ⟨hLen, i, hiLt, hiEq⟩
  have hi0 : i = 0 := (Nat.lt_one_iff.mp hiLt)
  subst hi0
  -- Now we have: (['a','b','c','a'])[0]! = (['a','b','c','a'])[1]!
  -- but these are 'a' and 'b'
  simpa using hiEq

theorem test1_postcondition_3 : ¬repeatsAt ['a', 'b', 'c', 'a'] 2 := by
  intro hRep2
  rcases hRep2 with ⟨hLen2, i, hiLt, hiEq⟩
  have hiCases : i = 0 ∨ i = 1 := by
    have hiLt' : i < 2 := hiLt
    omega
  cases hiCases with
  | inl hi0 =>
      subst hi0
      -- reduces to 'a' = 'c'
      simpa using hiEq
  | inr hi1 =>
      subst hi1
      -- reduces to 'b' = 'c'
      simpa using hiEq

theorem test1_postcondition_4
    (hNotRep0 : ¬repeatsAt ['a', 'b', 'c', 'a'] 0)
    (hNotRep1 : ¬repeatsAt ['a', 'b', 'c', 'a'] 1)
    (hNotRep2 : ¬repeatsAt ['a', 'b', 'c', 'a'] 2)
    : noRepeatBefore ['a', 'b', 'c', 'a'] 3 := by
  unfold noRepeatBefore
  intro k hk
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by
    omega
  rcases hk' with rfl | rfl | rfl
  · exact hNotRep0
  · exact hNotRep1
  · exact hNotRep2

theorem test1_postcondition_5
    (hNotRep0 : ¬repeatsAt ['a', 'b', 'c', 'a'] 0)
    (hNotRep1 : ¬repeatsAt ['a', 'b', 'c', 'a'] 1)
    (hNotRep2 : ¬repeatsAt ['a', 'b', 'c', 'a'] 2)
    : ∀ (j : ℕ), repeatsAt ['a', 'b', 'c', 'a'] j → noRepeatBefore ['a', 'b', 'c', 'a'] j → j = 3 := by
  intro j hjRep hjNoBefore
  have hjlt : j < (['a', 'b', 'c', 'a'] : List Char).length := hjRep.1
  have hjlt4 : j < 4 := by simpa using hjlt
  have hjle3 : j ≤ 3 := Nat.le_of_lt_succ (n := 3) (by simpa using hjlt4)

  -- rule out j = 0,1,2 using the given non-repeat facts
  have hne0 : j ≠ 0 := by
    intro hj0
    have : repeatsAt ['a', 'b', 'c', 'a'] 0 := by simpa [hj0] using hjRep
    exact hNotRep0 this
  have hne1 : j ≠ 1 := by
    intro hj1
    have : repeatsAt ['a', 'b', 'c', 'a'] 1 := by simpa [hj1] using hjRep
    exact hNotRep1 this
  have hne2 : j ≠ 2 := by
    intro hj2
    have : repeatsAt ['a', 'b', 'c', 'a'] 2 := by simpa [hj2] using hjRep
    exact hNotRep2 this

  -- from j ≤ 3 and j ≠ 0,1,2, conclude j = 3
  have hge3 : 3 ≤ j := by
    omega
  exact Nat.le_antisymm hjle3 hge3

theorem test1_postcondition_6
    (c : Char)
    (j : ℕ)
    (hj : j = 3)
    (hL : True)
    (hNotAllNoRep : ∃ x, repeatsAt ['a', 'b', 'c', 'a'] x)
    (hPartA : ∃ x, repeatsAt ['a', 'b', 'c', 'a'] x)
    (hIndex3 : True)
    (hjVal : ['a', 'b', 'c', 'a'][j]?.getD 'A' = c)
    : c = 'a' := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition : postcondition test1_s test1_Expected := by
  -- Unfold concrete inputs
  simp [test1_s, test1_Expected, postcondition]
  -- After simp, the goal is a conjunction for l := ("abca").toList.
  -- We make l explicit as the concrete list.
  have hL : ("abca" : String).toList = (['a', 'b', 'c', 'a'] : List Char) := by
    (try simp at *; expose_names); exact rfl; done
  -- Rewrite everything in terms of the concrete list
  -- (We keep `l` implicit via rewriting the computed toList.)
  -- Part A: (some 'a' = none ↔ ∀ j, ¬repeatsAt l j)
  have hRep3 : repeatsAt (['a', 'b', 'c', 'a'] : List Char) 3 := by
    -- show 3 < length and choose i = 0 with same element
    (try simp at *; expose_names); exact (test1_postcondition_0); done
  have hNotAllNoRep : ¬ (∀ j : Nat, ¬ repeatsAt (['a', 'b', 'c', 'a'] : List Char) j) := by
    -- contradict using j = 3
    (try simp at *; expose_names); exact Exists.intro 3 hRep3; done
  have hPartA :
      (some 'a' = (none : Option Char) ↔
        (∀ j : Nat, ¬ repeatsAt (['a', 'b', 'c', 'a'] : List Char) j)) := by
    -- left side is false; right side is false
    (try simp at *; expose_names); exact hNotAllNoRep; done

  -- Part B: ∀ c, some 'a' = some c ↔ ∃ j, repeatsAt l j ∧ noRepeatBefore l j ∧ l[j]! = c
  have hNotRep0 : ¬ repeatsAt (['a', 'b', 'c', 'a'] : List Char) 0 := by
    -- repeatsAt requires ∃ i, i < 0, impossible
    (try simp at *; expose_names); exact (test1_postcondition_1); done
  have hNotRep1 : ¬ repeatsAt (['a', 'b', 'c', 'a'] : List Char) 1 := by
    -- only i=0 possible; l[0] != l[1]
    (try simp at *; expose_names); exact (test1_postcondition_2); done
  have hNotRep2 : ¬ repeatsAt (['a', 'b', 'c', 'a'] : List Char) 2 := by
    -- i = 0 or 1 possible; neither equals l[2]
    (try simp at *; expose_names); exact (test1_postcondition_3); done
  have hNoRepeatBefore3 : noRepeatBefore (['a', 'b', 'c', 'a'] : List Char) 3 := by
    -- expand noRepeatBefore; show for k < 3, ¬repeatsAt l k; use cases k=0,1,2
    (try simp at *; expose_names); exact (test1_postcondition_4 hNotRep0 hNotRep1 hNotRep2); done
  have hIndex3 : ((['a', 'b', 'c', 'a'] : List Char)[3]!) = 'a' := by
    (try simp at *; expose_names); exact rfl; done

  have hOnlyRepIs3 :
      ∀ j : Nat, repeatsAt (['a', 'b', 'c', 'a'] : List Char) j → noRepeatBefore (['a', 'b', 'c', 'a'] : List Char) j → j = 3 := by
    -- in this concrete list, the first repeat occurs at index 3
    (try simp at *; expose_names); exact (test1_postcondition_5 hNotRep0 hNotRep1 hNotRep2); done

  have hPartB :
      ∀ c : Char,
        (some 'a' = some c ↔
          (∃ j : Nat,
            repeatsAt (['a', 'b', 'c', 'a'] : List Char) j ∧
              noRepeatBefore (['a', 'b', 'c', 'a'] : List Char) j ∧
                (['a', 'b', 'c', 'a'] : List Char)[j]! = c)) := by
    intro c
    constructor
    · intro hsc
      -- from some 'a' = some c get c = 'a', witness j = 3
      have hc : c = 'a' := by
        -- injectivity of Option.some
        (try simp at *; expose_names); exact id (Eq.symm hsc); done
      have hEq : (['a', 'b', 'c', 'a'] : List Char)[3]! = c := by
        -- rewrite using hIndex3 and hc
        (try simp at *; expose_names); exact hsc; done
      refine ⟨3, ?_, ?_, ?_⟩
      · exact hRep3
      · exact hNoRepeatBefore3
      · exact hEq
    · rintro ⟨j, hjRep, hjNoBefore, hjVal⟩
      -- show j = 3, hence c = 'a', hence some 'a' = some c
      have hj : j = 3 := by
        exact hOnlyRepIs3 j hjRep hjNoBefore
      have hc : c = 'a' := by
        -- use hjVal and hj and hIndex3
        (try simp at *; expose_names); exact (test1_postcondition_6 c j hj hL hNotAllNoRep hPartA hIndex3 hjVal); done
      -- conclude some 'a' = some c
      (try simp at *; expose_names); exact id (Eq.symm hc); done

  -- Conclude the conjunction, after rewriting l via hL
  -- We already `simp [test1_s, test1_Expected, postcondition]` at the start,
  -- so we now just need to supply the two parts specialized to the concrete list.
  refine And.intro ?_ ?_
  · -- Part A with l = ("abca").toList
    simpa [hL] using hPartA
  · -- Part B with l = ("abca").toList
    simpa [hL] using hPartB

theorem test5_precondition : precondition test5_s := by
    intros; expose_names; exact (trivial); done

theorem test5_postcondition_0 : repeatsAt ['a', 'b', 'b', 'c'] 2 := by
  -- unfold repeatsAt and prove both parts
  unfold repeatsAt
  constructor
  · -- bounds: 2 < length
    decide
  · -- witness i = 1
    refine ⟨1, ?_, ?_⟩
    · decide
    · simp

theorem test5_postcondition_1 : ¬repeatsAt ['a', 'b', 'b', 'c'] 0 := by
  intro h
  rcases h with ⟨_, i, hi0, _⟩
  exact (Nat.not_lt_zero i) hi0

theorem test5_postcondition_2 : ¬repeatsAt ['a', 'b', 'b', 'c'] 1 := by
  intro hRep1
  rcases hRep1 with ⟨hLen, i, hi, hEq⟩
  have hi0 : i = 0 := (Nat.lt_one_iff.mp hi)
  subst hi0
  -- now hEq says l[0]! = l[1]!, i.e., 'a' = 'b'
  simp [List.get!, List.get!_cons_zero, List.get!_cons_succ] at hEq

theorem test5_postcondition_3
    (hNotRep0 : ¬repeatsAt ['a', 'b', 'b', 'c'] 0)
    (hNotRep1 : ¬repeatsAt ['a', 'b', 'b', 'c'] 1)
    : noRepeatBefore ['a', 'b', 'b', 'c'] 2 := by
  unfold noRepeatBefore
  intro k hk
  have hk' : k = 0 ∨ k = 1 := by
    omega
  cases hk' with
  | inl hk0 =>
      simpa [hk0] using hNotRep0
  | inr hk1 =>
      simpa [hk1] using hNotRep1

theorem test5_postcondition_4
    (c : Char)
    (j : ℕ)
    (hj : j = 2)
    (hL : True)
    (hNotAllNoRep : ∃ x, repeatsAt ['a', 'b', 'b', 'c'] x)
    (hPartA : ∃ x, repeatsAt ['a', 'b', 'b', 'c'] x)
    (hIndex2 : True)
    (hjVal : ['a', 'b', 'b', 'c'][j]?.getD 'A' = c)
    : 'b' = c := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition : postcondition test5_s test5_Expected := by
  -- Step 1: unfold the concrete inputs and the postcondition
  simp [test5_s, test5_Expected, postcondition]

  -- Step 2: compute the concrete list l = ("abbc").toList
  have hL : ("abbc" : String).toList = (['a', 'b', 'b', 'c'] : List Char) := by
    (try simp at *; expose_names); exact rfl; done

  -- Step 6: exhibit a concrete repeat at j = 2 (witness i = 1)
  have hRep2 : repeatsAt (['a', 'b', 'b', 'c'] : List Char) 2 := by
    (try simp at *; expose_names); exact (test5_postcondition_0); done

  -- Step 5/6: show ¬(∀ j, ¬repeatsAt l j) by counterexample j = 2
  have hNotAllNoRep : ¬ (∀ j : Nat, ¬ repeatsAt (['a', 'b', 'b', 'c'] : List Char) j) := by
    (try simp at *; expose_names); exact Exists.intro 2 hRep2; done

  -- Step 5: Part A equivalence (left side false, right side false)
  have hPartA :
      (some 'b' = (none : Option Char) ↔
        (∀ j : Nat, ¬ repeatsAt (['a', 'b', 'b', 'c'] : List Char) j)) := by
    (try simp at *; expose_names); exact hNotAllNoRep; done

  -- Step 8.4(a): ¬repeatsAt l 0
  have hNotRep0 : ¬ repeatsAt (['a', 'b', 'b', 'c'] : List Char) 0 := by
    (try simp at *; expose_names); exact (test5_postcondition_1); done

  -- Step 8.4(b): ¬repeatsAt l 1
  have hNotRep1 : ¬ repeatsAt (['a', 'b', 'b', 'c'] : List Char) 1 := by
    (try simp at *; expose_names); exact (test5_postcondition_2); done

  -- Step 8.4: noRepeatBefore l 2
  have hNoRepeatBefore2 : noRepeatBefore (['a', 'b', 'b', 'c'] : List Char) 2 := by
    (try simp at *; expose_names); exact (test5_postcondition_3 hNotRep0 hNotRep1); done

  -- Step 8.5: compute the character at index 2
  have hIndex2 : ((['a', 'b', 'b', 'c'] : List Char)[2]!) = 'b' := by
    (try simp at *; expose_names); exact rfl; done

  -- Step 9.2: any repeat-index j that is "first" must be j = 2
  have hOnlyRepIs2 :
      ∀ j : Nat,
        repeatsAt (['a', 'b', 'b', 'c'] : List Char) j →
        noRepeatBefore (['a', 'b', 'b', 'c'] : List Char) j →
        j = 2 := by
    intro j hjRep hjNoBefore
    have hjLen : j < (['a', 'b', 'b', 'c'] : List Char).length := hjRep.1
    have hjLt4 : j < 4 := by
      simpa using hjLen
    have hjLe3 : j ≤ 3 := by
      omega
    have hne0 : j ≠ 0 := by
      intro hj0
      have : repeatsAt (['a', 'b', 'b', 'c'] : List Char) 0 := by simpa [hj0] using hjRep
      exact hNotRep0 this
    have hne1 : j ≠ 1 := by
      intro hj1
      have : repeatsAt (['a', 'b', 'b', 'c'] : List Char) 1 := by simpa [hj1] using hjRep
      exact hNotRep1 this
    have hne3 : j ≠ 3 := by
      intro hj3
      have hNoAt2 : ¬ repeatsAt (['a', 'b', 'b', 'c'] : List Char) 2 := by
        have : 2 < j := by simpa [hj3]
        exact hjNoBefore 2 this
      exact hNoAt2 hRep2
    have hjge2 : 2 ≤ j := by
      omega
    have hjle2 : j ≤ 2 := by
      omega
    exact Nat.le_antisymm hjle2 hjge2

  -- Step 7/8/9: Part B
  have hPartB :
      ∀ c : Char,
        (some 'b' = some c ↔
          (∃ j : Nat,
            repeatsAt (['a', 'b', 'b', 'c'] : List Char) j ∧
              noRepeatBefore (['a', 'b', 'b', 'c'] : List Char) j ∧
                (['a', 'b', 'b', 'c'] : List Char)[j]! = c)) := by
    intro c
    constructor
    · intro hsc
      have hc : c = 'b' := by
        -- use simp/injectivity: (some 'b' = some c) ↔ ('b' = c)
        -- then flip to get c = 'b'
        have hbEqc : 'b' = c := by
          (try simp at *; expose_names); exact hsc; done
        exact hbEqc.symm
      have hEq : (['a', 'b', 'b', 'c'] : List Char)[2]! = c := by
        (try simp at *; expose_names); exact hsc; done
      refine ⟨2, hRep2, hNoRepeatBefore2, hEq⟩
    · rintro ⟨j, hjRep, hjNoBefore, hjVal⟩
      have hj : j = 2 := hOnlyRepIs2 j hjRep hjNoBefore
      have hbEqc : 'b' = c := by
        -- rewrite hjVal using j = 2, then use hIndex2 to reduce to 'b' = c
        (try simp at *; expose_names); exact (test5_postcondition_4 c j hj hL hNotAllNoRep hPartA hIndex2 hjVal); done
      have hc : c = 'b' := hbEqc.symm
      -- conclude some 'b' = some c
      simpa [hc]

  -- Step 10: combine Part A and Part B, rewriting l via hL
  refine And.intro ?_ ?_
  · simpa [hL] using hPartA
  · simpa [hL] using hPartB

theorem test9_precondition : precondition test9_s := by
    intros; expose_names; exact (trivial); done

theorem test9_postcondition_0 : repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] 3 := by
  unfold repeatsAt
  constructor
  · decide
  · refine ⟨1, ?_, ?_⟩
    · decide
    · simp

theorem test9_postcondition_1 : ¬repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] 0 := by
  intro h
  rcases h with ⟨_, i, hiLt, _⟩
  exact (Nat.not_lt_zero i) hiLt

theorem test9_postcondition_2 : ¬repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] 1 := by
  intro hRep1
  rcases hRep1 with ⟨hLen, i, hiLt, hiEq⟩
  have hi0 : i = 0 := by
    exact (Nat.lt_one_iff.mp hiLt)
  subst hi0
  -- Now hiEq : l[0]! = l[1]!, but l[0]! = 'a' and l[1]! = 'b'
  simpa using hiEq

theorem test9_postcondition_3 : ¬repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] 2 := by
  intro hRep2
  rcases hRep2 with ⟨hLen, i, hiLt, hiEq⟩
  have hiCases : i = 0 ∨ i = 1 := by
    omega
  cases hiCases with
  | inl hi0 =>
      subst hi0
      -- hiEq : L[0]! = L[2]!
      -- but L[0]! = 'a' and L[2]! = 'c'
      simpa using (show ('a' : Char) = 'c' from by simpa using hiEq)
  | inr hi1 =>
      subst hi1
      -- hiEq : L[1]! = L[2]!
      -- but L[1]! = 'b' and L[2]! = 'c'
      simpa using (show ('b' : Char) = 'c' from by simpa using hiEq)

theorem test9_postcondition_4
    (hNotRep0 : ¬repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] 0)
    (hNotRep1 : ¬repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] 1)
    (hNotRep2 : ¬repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] 2)
    : noRepeatBefore ['a', 'b', 'c', 'b', 'a', 'd'] 3 := by
  unfold noRepeatBefore
  intro k hk
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by
    omega
  rcases hk' with h0 | h12
  · simpa [h0] using hNotRep0
  · rcases h12 with h1 | h2
    · simpa [h1] using hNotRep1
    · simpa [h2] using hNotRep2

theorem test9_postcondition_5
    (j : ℕ)
    (hjLt6 : j < 6)
    (hjLe5 : j ≤ 5)
    (hne0 : ¬j = 0)
    (hne1 : ¬j = 1)
    (hne2 : ¬j = 2)
    (hj4 : j = 4)
    (hL : True)
    (hNotAllNoRep : ∃ x, repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] x)
    (hPartA : ∃ x, repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] x)
    (hIndex3 : True)
    (hjLen : j < 6)
    : 3 < j := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test9_postcondition_6
    (j : ℕ)
    (hjLt6 : j < 6)
    (hjLe5 : j ≤ 5)
    (hne0 : ¬j = 0)
    (hne1 : ¬j = 1)
    (hne2 : ¬j = 2)
    (hne4 : ¬j = 4)
    (hj5 : j = 5)
    (hL : True)
    (hNotAllNoRep : ∃ x, repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] x)
    (hPartA : ∃ x, repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] x)
    (hIndex3 : True)
    (hjLen : j < 6)
    : 3 < j := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test9_postcondition_7
    (c : Char)
    (j : ℕ)
    (hj : j = 3)
    (hL : True)
    (hNotAllNoRep : ∃ x, repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] x)
    (hPartA : ∃ x, repeatsAt ['a', 'b', 'c', 'b', 'a', 'd'] x)
    (hIndex3 : True)
    (hjVal : ['a', 'b', 'c', 'b', 'a', 'd'][j]?.getD 'A' = c)
    : c = 'b' := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test9_postcondition : postcondition test9_s test9_Expected := by
  -- Step 1: unfold concrete inputs and postcondition
  simp [test9_s, test9_Expected, postcondition]

  -- Step 2: compute l = ("abcbad").toList
  have hL : ("abcbad" : String).toList = (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) := by
    (try simp at *; expose_names); exact rfl; done

  -- Step 4: exhibit a repeat at j = 3 (witness i = 1)
  have hRep3 : repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) 3 := by
    (try simp at *; expose_names); exact (test9_postcondition_0); done

  -- Step 5: show ¬(∀ j, ¬repeatsAt l j) using j = 3
  have hNotAllNoRep : ¬ (∀ j : Nat, ¬ repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) j) := by
    (try simp at *; expose_names); exact Exists.intro 3 hRep3; done

  -- Step 5: Part A (both sides false)
  have hPartA :
      (some 'b' = (none : Option Char) ↔
        (∀ j : Nat, ¬ repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) j)) := by
    (try simp at *; expose_names); exact hNotAllNoRep; done

  -- Step 6/7: ¬repeatsAt at indices 0,1,2
  have hNotRep0 : ¬ repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) 0 := by
    (try simp at *; expose_names); exact (test9_postcondition_1); done
  have hNotRep1 : ¬ repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) 1 := by
    (try simp at *; expose_names); exact (test9_postcondition_2); done
  have hNotRep2 : ¬ repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) 2 := by
    (try simp at *; expose_names); exact (test9_postcondition_3); done

  -- Step 7: package into noRepeatBefore l 3
  have hNoRepeatBefore3 : noRepeatBefore (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) 3 := by
    (try simp at *; expose_names); exact (test9_postcondition_4 hNotRep0 hNotRep1 hNotRep2); done

  -- Step 6: compute l[3]!
  have hIndex3 : ((['a', 'b', 'c', 'b', 'a', 'd'] : List Char)[3]!) = 'b' := by
    (try simp at *; expose_names); exact rfl; done

  -- Step 9: if j is a repeat index and no repeats before it, then j = 3
  have hOnlyRepIs3 :
      ∀ j : Nat,
        repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) j →
        noRepeatBefore (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) j →
        j = 3 := by
    intro j hjRep hjNoBefore
    have hjLen : j < (['a', 'b', 'c', 'b', 'a', 'd'] : List Char).length := hjRep.1
    have hjLt6 : j < 6 := by
      -- length is 6
      (try simp at *; expose_names); exact hjLen; done
    have hjLe5 : j ≤ 5 := by
      (try simp at *; expose_names); exact Nat.le_of_lt_succ hjLt6; done
    have hne0 : j ≠ 0 := by
      intro hj0
      have : repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) 0 := by
        simpa [hj0] using hjRep
      exact hNotRep0 this
    have hne1 : j ≠ 1 := by
      intro hj1
      have : repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) 1 := by
        simpa [hj1] using hjRep
      exact hNotRep1 this
    have hne2 : j ≠ 2 := by
      intro hj2
      have : repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) 2 := by
        simpa [hj2] using hjRep
      exact hNotRep2 this
    have hne4 : j ≠ 4 := by
      intro hj4
      have hNoAt3 : ¬ repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) 3 := by
        have : 3 < j := by
          -- from j = 4
          (try simp at *; expose_names); exact (test9_postcondition_5 j hjLt6 hjLe5 hne0 hne1 hne2 hj4 hL hNotAllNoRep hPartA hIndex3 hjLen); done
        exact hjNoBefore 3 this
      exact hNoAt3 hRep3
    have hne5 : j ≠ 5 := by
      intro hj5
      have hNoAt3 : ¬ repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) 3 := by
        have : 3 < j := by
          -- from j = 5
          (try simp at *; expose_names); exact (test9_postcondition_6 j hjLt6 hjLe5 hne0 hne1 hne2 hne4 hj5 hL hNotAllNoRep hPartA hIndex3 hjLen); done
        exact hjNoBefore 3 this
      exact hNoAt3 hRep3
    have hjLe3 : j ≤ 3 := by
      -- with j ≤ 5 and j ≠ 4,5, we get j ≤ 3
      (try simp at *; expose_names); exact Nat.le_of_not_lt fun a ↦ hjNoBefore 3 a hRep3; done
    have hjGe3 : 3 ≤ j := by
      -- with j ≠ 0,1,2 we get 3 ≤ j
      (try simp at *; expose_names); exact Nat.le_of_not_lt fun a ↦ hNoRepeatBefore3 j a hjRep; done
    exact Nat.le_antisymm hjLe3 hjGe3

  -- Step 8/9: Part B equivalence
  have hPartB :
      ∀ c : Char,
        (some 'b' = some c ↔
          (∃ j : Nat,
            repeatsAt (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) j ∧
              noRepeatBefore (['a', 'b', 'c', 'b', 'a', 'd'] : List Char) j ∧
                (['a', 'b', 'c', 'b', 'a', 'd'] : List Char)[j]! = c)) := by
    intro c
    constructor
    · intro hsc
      have hc : c = 'b' := by
        -- injectivity of Option.some
        (try simp at *; expose_names); exact id (Eq.symm hsc); done
      have hEq : (['a', 'b', 'c', 'b', 'a', 'd'] : List Char)[3]! = c := by
        -- rewrite using hc and hIndex3
        (try simp at *; expose_names); exact hsc; done
      refine ⟨3, ?_, ?_, ?_⟩
      · exact hRep3
      · exact hNoRepeatBefore3
      · exact hEq
    · rintro ⟨j, hjRep, hjNoBefore, hjVal⟩
      have hj : j = 3 := by
        exact hOnlyRepIs3 j hjRep hjNoBefore
      have hc : c = 'b' := by
        -- rewrite hjVal using hj, then use hIndex3
        (try simp at *; expose_names); exact (test9_postcondition_7 c j hj hL hNotAllNoRep hPartA hIndex3 hjVal); done
      -- conclude some 'b' = some c
      simpa [hc]

  -- Step 10: combine Part A and Part B, rewriting l using hL
  refine And.intro ?_ ?_
  · simpa [hL] using hPartA
  · simpa [hL] using hPartB

theorem uniqueness
    (s : String)
    : precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  classical
  -- unpack postconditions
  unfold postcondition at hpost1 hpost2
  let l := s.toList
  have h1 :
      ((ret1 = none ↔ (∀ j : Nat, ¬repeatsAt l j)) ∧
        (∀ c : Char,
          ret1 = some c ↔
            (∃ j : Nat, repeatsAt l j ∧ noRepeatBefore l j ∧ l[j]! = c))) := by
    simpa [l] using hpost1
  have h2 :
      ((ret2 = none ↔ (∀ j : Nat, ¬repeatsAt l j)) ∧
        (∀ c : Char,
          ret2 = some c ↔
            (∃ j : Nat, repeatsAt l j ∧ noRepeatBefore l j ∧ l[j]! = c))) := by
    simpa [l] using hpost2

  have hnone1 : (ret1 = none ↔ (∀ j : Nat, ¬repeatsAt l j)) := h1.1
  have hsome1 :
      ∀ c : Char,
        ret1 = some c ↔ (∃ j : Nat, repeatsAt l j ∧ noRepeatBefore l j ∧ l[j]! = c) := h1.2
  have hnone2 : (ret2 = none ↔ (∀ j : Nat, ¬repeatsAt l j)) := h2.1
  have hsome2 :
      ∀ c : Char,
        ret2 = some c ↔ (∃ j : Nat, repeatsAt l j ∧ noRepeatBefore l j ∧ l[j]! = c) := h2.2

  let P : Prop := ∀ j : Nat, ¬repeatsAt l j

  by_cases hP : P
  · have hr1 : ret1 = none := hnone1.mpr (by simpa [P] using hP)
    have hr2 : ret2 = none := hnone2.mpr (by simpa [P] using hP)
    simpa [hr1, hr2]
  · have hr1ne : ret1 ≠ none := by
      intro hEq
      have : (∀ j : Nat, ¬repeatsAt l j) := hnone1.mp hEq
      exact hP (by simpa [P] using this)
    have hr2ne : ret2 ≠ none := by
      intro hEq
      have : (∀ j : Nat, ¬repeatsAt l j) := hnone2.mp hEq
      exact hP (by simpa [P] using this)

    rcases (Option.ne_none_iff_exists'.1 hr1ne) with ⟨c1, hc1⟩
    rcases (Option.ne_none_iff_exists'.1 hr2ne) with ⟨c2, hc2⟩
    subst hc1
    subst hc2

    have hex1 :
        ∃ j : Nat, repeatsAt l j ∧ noRepeatBefore l j ∧ l[j]! = c1 := by
      exact (hsome1 c1).mp rfl
    have hex2 :
        ∃ j : Nat, repeatsAt l j ∧ noRepeatBefore l j ∧ l[j]! = c2 := by
      exact (hsome2 c2).mp rfl

    rcases hex1 with ⟨j1, hj1rep, hj1nrb, hj1val⟩
    rcases hex2 with ⟨j2, hj2rep, hj2nrb, hj2val⟩

    have hj1le : j1 ≤ j2 := by
      by_contra h
      have hj2lt : j2 < j1 := Nat.lt_of_not_ge h
      have : ¬repeatsAt l j2 := hj1nrb j2 hj2lt
      exact this hj2rep
    have hj2le : j2 ≤ j1 := by
      by_contra h
      have hj1lt : j1 < j2 := Nat.lt_of_not_ge h
      have : ¬repeatsAt l j1 := hj2nrb j1 hj1lt
      exact this hj1rep
    have hj : j1 = j2 := Nat.le_antisymm hj1le hj2le

    have hc : c1 = c2 := by
      -- hj2val : l[j2]! = c2, rewrite j2 to j1
      have hj2val' : l[j1]! = c2 := by simpa [hj] using hj2val
      -- hj1val : l[j1]! = c1
      -- so c1 = c2
      exact (hj1val.symm.trans hj2val')

    simpa [hc]
end Proof
