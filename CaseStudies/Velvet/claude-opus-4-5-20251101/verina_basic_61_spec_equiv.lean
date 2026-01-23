/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e46c35e0-b4d5-4fdc-af3a-32ebcaae62eb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String):
  VerinaSpec.allDigits_precond s ↔ LeetProofSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.allDigits_precond s):
  VerinaSpec.allDigits_postcond s result h_precond ↔ LeetProofSpec.postcondition s result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isDigit (c : Char) : Bool :=
  (c ≥ '0') && (c ≤ '9')

def allDigits_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def allDigits_postcond (s : String) (result: Bool) (h_precond : allDigits_precond (s)) :=
  -- !benchmark @start postcond
  (result = true ↔ ∀ c ∈ s.toList, isDigit c)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions
-- Using String.all from Mathlib/Init which checks if all characters satisfy a predicate
-- Using Char.isDigit which checks if a character is a digit ('0' to '9')

-- Postcondition: result is true iff all characters are digits
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ s.all Char.isDigit = true

-- Alternative characterization: result matches String.all with isDigit predicate
def ensures2 (s : String) (result : Bool) :=
  result = s.all Char.isDigit

def precondition (s : String) :=
  True

-- no preconditions needed

def postcondition (s : String) (result : Bool) :=
  ensures2 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.allDigits_precond s ↔ LeetProofSpec.precondition s := by
  -- Since both preconditions are defined as True, the equivalence is trivial.
  simp [VerinaSpec.allDigits_precond, LeetProofSpec.precondition]

noncomputable section AristotleLemmas

theorem verina_isDigit_eq_char_isDigit (c : Char) : VerinaSpec.isDigit c = c.isDigit := by
  -- By definition of `isDigit`, we know that `VerinaSpec.isDigit c` is true if and only if `c` is a digit.
  simp [VerinaSpec.isDigit, Char.isDigit];
  -- Since '0' is 48 and '9' is 57 in ASCII, the inequalities 48 ≤ c and c ≤ 57 are equivalent to '0' ≤ c and c ≤ '9'.
  simp [Char.le_def, Char.ofNat]

#print String.all
#print String.any

#print String
#print String.toList

#print String.Pos
#print String.get
#print String.next

theorem list_all_eq_true_iff_forall (l : List α) (p : α → Bool) : l.all p = true ↔ ∀ x ∈ l, p x = true := by
  -- By definition of `all`, we know that `l.all p` is true if and only if every element in `l` satisfies `p`. Therefore, the equivalence holds by definition.
  simp [List.all]

#print String.anyAux
#print String.endPos
#print String.utf8GetAux

theorem string_nil_all (p : Char → Bool) : (String.mk []).all p = true := by
  -- The all function for the empty string is true by definition.
  simp [String.all];
  -- The empty string has no characters, so the any function returns false.
  simp [String.any];
  simp +decide [ String.anyAux ]

lemma utf8GetAux_shift (cs : List Char) (pos target : String.Pos) (delta : String.Pos) : String.utf8GetAux cs (pos + delta) (target + delta) = String.utf8GetAux cs pos target := by
  induction' cs with c cs ih generalizing pos target delta <;> simp +arith +decide [ *, String.utf8GetAux ];
  -- Since adding the same delta to both pos and target doesn't change their equality, the if conditions are equivalent.
  simp [String.Pos.ext_iff] at *;
  -- Since addition is associative, we can rewrite the left-hand side to match the right-hand side using the associativity of addition.
  have h_assoc : pos + delta + c = pos + c + delta := by
    simp +decide [ add_comm, add_left_comm, add_assoc, String.Pos.ext_iff ];
  aesop

lemma get_cons_shift (c : Char) (cs : List Char) (i : String.Pos) : (String.mk (c :: cs)).get (i + c) = (String.mk cs).get i := by
  -- Since the length of `c :: cs` is at least 1, we can apply the definition of `String.get` directly.
  simp [String.get];
  -- By definition of `utf8GetAux`, when the position is 0, it returns the first element of the list.
  simp [String.utf8GetAux];
  split_ifs <;> simp_all +decide [ String.Pos.ext_iff ];
  · exact absurd ‹_› ( ne_of_lt ( add_pos_of_nonneg_of_pos ( Nat.zero_le _ ) ( Char.utf8Size_pos _ ) ) );
  · -- By definition of `utf8GetAux`, shifting the position by `c` and then taking the first element is the same as taking the first element and then shifting the position by `c`.
    have h_shift : ∀ (cs : List Char) (pos : String.Pos) (target : String.Pos) (delta : String.Pos), String.utf8GetAux cs (pos + delta) (target + delta) = String.utf8GetAux cs pos target := by
      exact?;
    exact h_shift _ _ _ _

lemma next_cons_shift (c : Char) (cs : List Char) (i : String.Pos) : (String.mk (c :: cs)).next (i + c) = (String.mk cs).next i + c := by
  -- By definition of `String.next`, we have that `String.next (String.mk (c :: cs)) (i + c)` is the position after `i + c` in the string `c :: cs`.
  simp [String.next];
  -- By definition of `get`, we know that `get (i + c) (c :: cs)` is the same as `get i cs` because `i + c` is the position after `c`.
  have h_get_shift : String.get (String.mk (c :: cs)) (i + c) = String.get (String.mk cs) i := by
    exact?;
  simp_all +decide [ add_comm, add_left_comm, add_assoc ];
  exact?

#print String.utf8ByteSize
#print String.endPos

lemma endPos_cons (c : Char) (cs : List Char) : (String.mk (c :: cs)).endPos = (String.mk cs).endPos + c := by
  simp [String.endPos, String.utf8ByteSize]
  -- We need to show utf8ByteSize (c :: cs) = utf8ByteSize cs + c.utf8Size
  -- String.utf8ByteSize is defined via go
  -- String.utf8ByteSize.go (c :: cs) = c.utf8Size + String.utf8ByteSize.go cs
  -- This should be true by definition.
  -- We need to check String.Pos addition.
  -- String.Pos.mk (a + b) = String.Pos.mk a + String.Pos.mk b ?
  -- Or rather String.Pos.mk a + c = String.Pos.mk (a + c.utf8Size)
  apply String.Pos.ext
  simp [String.Pos.byteIdx]
  -- We need to unfold utf8ByteSize.go
  -- It seems utf8ByteSize.go is not easily accessible or I need to find the lemma for it.
  -- Actually, String.utf8ByteSize is defined by pattern matching on String.
  -- Let's try to prove utf8ByteSize_cons first if needed.
  -- By definition of `String.utf8ByteSize.go`, we can split the list into the head `c` and the tail `cs`.
  simp [String.utf8ByteSize.go]

#check (0 : String.Pos) + 'a'
#print String.Pos
#print String.next

lemma anyAux_shift_general (s1 s2 : String) (stop : String.Pos) (delta : String.Pos) (p : Char → Bool) (i : String.Pos)
  (h_get : ∀ k, k < stop → s1.get (k + delta) = s2.get k) :
  s1.anyAux (stop + delta) p (i + delta) = s2.anyAux stop p i := by
    -- By definition of `anyAux`, we can rewrite the goal using the induction hypothesis.
    have h_anyAux : ∀ (s : String) (stop : String.Pos) (p : Char → Bool) (i : String.Pos), s.anyAux stop p i = if i < stop then p (s.get i) || s.anyAux stop p (s.next i) else false := by
      intros s stop p i; exact (by
      rw [String.anyAux];
      grind);
    induction' n : ( stop + delta ).byteIdx - ( i + delta ).byteIdx using Nat.strong_induction_on with n ih generalizing i;
    by_cases hi : ( i + delta ) < ( stop + delta ) <;> by_cases hi' : i < stop <;> simp +decide [ hi, hi', h_anyAux s1 ( stop + delta ) p ( i + delta ), h_anyAux s2 stop p i ];
    · rw [ h_get i hi' ];
      -- By the induction hypothesis, since the difference between (stop + delta).byteIdx and (s1.next (i + delta)).byteIdx is less than n, we have s1.anyAux (stop + delta) p (s1.next (i + delta)) = s2.anyAux stop p (s2.next i).
      have h_ind : s1.anyAux (stop + delta) p (s1.next (i + delta)) = s2.anyAux stop p (s2.next i) := by
        convert ih _ _ _ rfl using 1;
        · congr! 1;
          -- By the properties of the next function and the hypothesis h_get, we can conclude that s1.next (i + delta) = s2.next i + delta.
          have h_next : s1.next (i + delta) = (i + delta) + s1.get (i + delta) := by
            exact?;
          rw [ h_next, h_get i hi' ];
          -- By the properties of addition, we can rearrange the terms to show that both sides are equal.
          have h_add_comm : ∀ (a b c : String.Pos), a + b + c = a + c + b := by
            intros a b c; exact (by
            exact String.Pos.ext ( by simp +decide [ add_comm, add_left_comm, add_assoc ] ));
          exact h_add_comm _ _ _;
        · rw [ ← n ];
          refine' Nat.sub_lt_sub_left _ _;
          · exact hi;
          · simp +decide [ String.next ];
            exact Char.utf8Size_pos _;
      rw [ h_ind ];
    · contrapose! hi';
      rw [ String.Pos.lt_iff ] at *;
      exact?;
    · contrapose! hi;
      exact Nat.add_lt_add_right hi' _

lemma anyAux_shift_general_nat (s1 s2 : String) (stop : String.Pos) (delta : Nat) (p : Char → Bool) (i : String.Pos)
  (h_get : ∀ k, k < stop → s1.get ⟨k.byteIdx + delta⟩ = s2.get k) :
  s1.anyAux ⟨stop.byteIdx + delta⟩ p ⟨i.byteIdx + delta⟩ = s2.anyAux stop p i := by
    -- Apply the hypothesis `h_get` to conclude that the anyAux functions are equal.
    apply anyAux_shift_general;
    -- Apply the hypothesis `h_get` directly to conclude the proof.
    intros k hk
    apply h_get k hk

lemma pos_add_mk_eq (p : String.Pos) (d : Nat) : p + String.Pos.mk d = String.Pos.mk (p.byteIdx + d) := by
  cases p
  rfl

lemma pos_add_char_eq_mk (p : String.Pos) (c : Char) : p + c = ⟨p.byteIdx + c.utf8Size⟩ := by
  cases p
  rfl

lemma anyAux_shift_general_v2 (s1 s2 : String) (stop : String.Pos) (delta : Nat) (p : Char → Bool) (i : String.Pos)
  (h_get : ∀ k, k < stop → s1.get ⟨k.byteIdx + delta⟩ = s2.get k) :
  s1.anyAux ⟨stop.byteIdx + delta⟩ p ⟨i.byteIdx + delta⟩ = s2.anyAux stop p i := by
    -- Apply the lemma anyAux_shift_general with the given hypothesis h_get.
    apply anyAux_shift_general_nat; assumption

lemma anyAux_shift (c : Char) (cs : List Char) (p : Char → Bool) (i : String.Pos) :
  String.anyAux (String.mk (c :: cs)) ((String.mk cs).endPos + c) p (i + c) =
  String.anyAux (String.mk cs) (String.endPos (String.mk cs)) p i := by
  rw [pos_add_char_eq_mk ((String.mk cs).endPos) c]
  rw [pos_add_char_eq_mk i c]
  apply anyAux_shift_general_v2
  intros k hk
  rw [← pos_add_char_eq_mk k c]
  apply get_cons_shift

lemma string_cons_any (c : Char) (cs : List Char) (p : Char → Bool) :
  (String.mk (c :: cs)).any p = (p c || (String.mk cs).any p) := by
    -- By definition of `anyAux`, we can split the string into the first character and the rest, and apply `anyAux` to the rest. This follows directly from the definition of `anyAux`.
    have h_split : String.anyAux (String.mk (c :: cs)) (String.endPos (String.mk (c :: cs))) p 0 = if p c = Bool.true then Bool.true else String.anyAux (String.mk cs) (String.endPos (String.mk cs)) p 0 := by
      rw [ String.anyAux ];
      split_ifs <;> simp_all +decide [ String.next ];
      · simp_all +decide [ String.get ];
        simp_all +decide [ String.utf8GetAux ];
      · cases ‹p c = Bool.true›.symm.trans ‹p ( String.get ( String.mk ( c :: cs ) ) 0 ) = Bool.false›;
      · convert anyAux_shift c cs p 0 using 1;
      · simp_all +decide [ String.endPos ];
        simp_all +decide [ String.utf8ByteSize ];
        simp_all +decide [ String.utf8ByteSize.go ];
        exact absurd ( ‹String.utf8ByteSize.go cs = 0 ∧ c.utf8Size = 0›.2 ) ( by exact ne_of_gt ( Char.utf8Size_pos c ) );
      · cases cs <;> simp_all +decide [ String.endPos ];
        · simp_all +decide [ String.utf8ByteSize ];
          simp_all +decide [ String.utf8ByteSize.go ];
          exact absurd ‹_› ( by exact ne_of_gt ( Char.utf8Size_pos c ) );
        · simp_all +decide [ String.utf8ByteSize ];
          simp_all +decide [ String.utf8ByteSize.go ];
          exact absurd ( ‹ ( String.utf8ByteSize.go _ = 0 ∧ _ ) ∧ _›.2 ) ( by exact ne_of_gt ( Char.utf8Size_pos _ ) );
    aesop

theorem string_all_eq_list_all (s : String) (p : Char → Bool) : s.all p = s.toList.all p := by
  -- By definition of `String.all`, we can rewrite it using the `any` function and De Morgan's laws. Specifically, `String.all` is defined as `¬String.any (fun c => ¬p c)`.
  have h_all_def : ∀ (s : String) (p : Char → Bool), s.all p = ¬s.any (fun c => ¬p c) := by
    unfold String.all String.any; aesop;
  unfold String.any at h_all_def;
  -- By definition of `String.anyAux`, we can see that it is equivalent to the `any` function on the list of characters.
  have h_anyAux_eq_any : ∀ (cs : List Char) (p : Char → Bool), String.anyAux (String.mk cs) (String.endPos (String.mk cs)) p 0 = List.any cs p := by
    -- We'll use induction on the list `cs`.
    intro cs p
    induction' cs with c cs ih;
    · simp +decide [ String.anyAux ];
    · -- By definition of `anyAux`, we can split the list into the head `c` and the tail `cs`.
      have h_split : String.anyAux (String.mk (c :: cs)) (String.endPos (String.mk (c :: cs))) p 0 = (p c || String.anyAux (String.mk cs) (String.endPos (String.mk cs)) p 0) := by
        -- Apply the lemma `string_cons_any` with the appropriate parameters.
        apply string_cons_any;
      aesop;
  -- Apply the definition of `String.anyAux` from `h_anyAux_eq_any`.
  specialize h_anyAux_eq_any s.data (fun c => ¬p c);
  cases h : s.all p <;> aesop

end AristotleLemmas

theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.allDigits_precond s):
  VerinaSpec.allDigits_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  simp_all +decide [ LeetProofSpec.postcondition, LeetProofSpec.ensures2 ];
  -- By definition of `VerinaSpec.allDigits_postcond`, we can rewrite the left-hand side of the equivalence.
  simp [VerinaSpec.allDigits_postcond];
  -- By definition of `String.all`, we know that `s.all Char.isDigit` is true if and only if every character in `s` satisfies `Char.isDigit`.
  have h_all : s.all Char.isDigit = s.toList.all Char.isDigit := by
    exact?;
  -- By definition of `Char.isDigit`, we know that `Char.isDigit c` is true if and only if `c` is a digit.
  have h_char_isDigit : ∀ c : Char, Char.isDigit c = (c ≥ '0' ∧ c ≤ '9') := by
    unfold Char.isDigit; aesop;
  simp_all +decide [ VerinaSpec.isDigit ];
  grind
