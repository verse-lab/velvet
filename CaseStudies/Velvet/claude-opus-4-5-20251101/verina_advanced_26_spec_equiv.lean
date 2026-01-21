/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: db5e6c1c-c718-4aa5-9aba-a2c345173b5e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (digits : String):
  VerinaSpec.letterCombinations_precond digits ↔ LeetProofSpec.precondition digits

- theorem postcondition_equiv (digits : String) (result : List String) (h_precond : VerinaSpec.letterCombinations_precond digits):
  VerinaSpec.letterCombinations_postcond digits result h_precond ↔ LeetProofSpec.postcondition digits result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []

@[reducible]
def letterCombinations_precond (digits : String) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def letterCombinations_postcond (digits : String) (result: List String) (h_precond : letterCombinations_precond (digits)) : Prop :=
  -- !benchmark @start postcond
  if digits.isEmpty then
    result = []
  else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then
    result = []
  else
    let expected := digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [""]
    result.length = expected.length ∧ result.all (λ s => s ∈ expected) ∧ expected.all (λ s => s ∈ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Mapping from digit character to list of corresponding letters
def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []

-- Check if a digit is valid (maps to letters)
def isValidDigit (c : Char) : Bool :=
  (digitToLetters c).length > 0

-- Check if all digits in the string are valid
def allValidDigits (s : String) : Bool :=
  s.data.all isValidDigit

-- Precondition: no restrictions on input
def precondition (digits : String) :=
  True

-- Postcondition: property-based specification without recursive reference implementation
def postcondition (digits : String) (result : List String) :=
  -- If input is empty, result is empty
  (digits.isEmpty → result = []) ∧
  -- If any digit is invalid, result is empty
  (¬digits.isEmpty → ¬allValidDigits digits → result = []) ∧
  -- If input is non-empty and all digits are valid:
  (¬digits.isEmpty → allValidDigits digits →
    -- Result length equals product of letter counts
    result.length = (digits.data.map (fun c => (digitToLetters c).length)).foldl (· * ·) 1 ∧
    -- Each result string has correct length
    (∀ i : Nat, i < result.length → (result[i]!).length = digits.length) ∧
    -- Each result string is a valid combination (each char comes from correct digit mapping)
    (∀ i : Nat, i < result.length →
      ∀ j : Nat, j < digits.length →
        (result[i]!).data[j]! ∈ digitToLetters (digits.data[j]!)) ∧
    -- No duplicates
    result.Nodup ∧
    -- All valid combinations are covered (every valid combination appears in result)
    (∀ combo : List Char, combo.length = digits.length →
      (∀ j : Nat, j < digits.length → combo[j]! ∈ digitToLetters (digits.data[j]!)) →
      combo.asString ∈ result))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (digits : String):
  VerinaSpec.letterCombinations_precond digits ↔ LeetProofSpec.precondition digits := by
  -- Since both preconditions are always true, the equivalence holds trivially.
  simp [VerinaSpec.letterCombinations_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (digits : String) (result : List String) (h_precond : VerinaSpec.letterCombinations_precond digits):
  VerinaSpec.letterCombinations_postcond digits result h_precond ↔ LeetProofSpec.postcondition digits result := by
  -- Let's split the proof into two implications.
  apply Iff.intro;
  · unfold VerinaSpec.letterCombinations_postcond LeetProofSpec.postcondition;
    split_ifs <;> simp_all +decide [ LeetProofSpec.allValidDigits ];
    · -- If the result is empty, then the foldl of the lengths of the letters for each digit must be 0, which contradicts the assumption that all digits are valid.
      intros h_empty h_valid
      have h_contra : ∃ x ∈ digits.data, ¬(LeetProofSpec.isValidDigit x) := by
        -- Since `digits.data` contains an element that is not in `['2', '3', '4', '5', '6', '7', '8', '9']`, we can use this element as the witness.
        obtain ⟨x, hx⟩ : ∃ x ∈ digits.data, ¬(x ∈ ['2', '3', '4', '5', '6', '7', '8', '9']) := by
          aesop;
        simp_all +decide [ LeetProofSpec.isValidDigit ];
        exact absurd ( h_valid x hx.1 ) ( by rw [ show LeetProofSpec.digitToLetters x = [] from by { unfold LeetProofSpec.digitToLetters; aesop } ] ; decide );
      aesop;
    · intro hp hp_1 hq
      constructor;
      · intro x hx hx'; specialize ‹∀ x ∈ digits.data, ¬x = '2' → ¬x = '3' → ¬x = '4' → ¬x = '5' → ¬x = '6' → ¬x = '7' → ¬x = '8' → x = '9'› x hx; simp_all +decide [ LeetProofSpec.isValidDigit ] ;
        unfold LeetProofSpec.digitToLetters at hx'; aesop;
      · intro h;
        refine' ⟨ _, _, _, _, _ ⟩;
        · induction' digits.data using List.reverseRecOn with c cs ih <;> aesop;
        · intro i hi;
          -- By definition of `List.foldl`, the length of each string in the result is equal to the length of `digits`.
          have h_foldl_length : ∀ (ds : List Char), (∀ d ∈ ds, LeetProofSpec.isValidDigit d = Bool.true) → ∀ (s : String), s ∈ List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) [""] (List.map VerinaSpec.digitToLetters ds) → s.length = ds.length := by
            intro ds hds; induction' ds using List.reverseRecOn with ds ih <;> aesop;
          exact h_foldl_length _ h _ ( hp_1 _ ( by simp ) );
        · intro i hi j hj;
          have h_comb : ∀ (ds : List (List Char)), ∀ (s : String), s ∈ List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) [""] ds → ∀ (j : ℕ), j < ds.length → (s.data[j]?.getD 'A') ∈ ds[j]?.getD [] := by
            intros ds s hs j hj; induction' ds using List.reverseRecOn with ds ih generalizing s j; aesop;
            by_cases hj' : j < ds.length <;> simp_all +decide [ List.getElem?_append ];
            · -- Since $s$ is the concatenation of $a$ and $a_1$, and $a$ is in the foldl of $ds$, the $j$-th element of $s$ is the same as the $j$-th element of $a$.
              obtain ⟨a, ha, a_1, ha_1, hs_eq⟩ := hs;
              have h_jth : s.data[j]?.getD 'A' = a.data[j]?.getD 'A' := by
                rw [ ← hs_eq ];
                simp +decide [ List.getElem?_append, hj' ];
                split_ifs <;> simp_all +decide [ List.getElem?_eq_none ];
                -- Since $j - a.data.length \geq 1$, the element at position $j - a.data.length$ in the list $[a_1]$ is out of bounds, so it returns the default value 'A'.
                have h_out_of_bounds : j - a.data.length ≥ 1 := by
                  refine' Nat.sub_pos_of_lt ( lt_of_le_of_ne ‹_› _ );
                  have h_contra : ∀ (ds : List (List Char)), ∀ (s : String), s ∈ List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) [""] ds → s.data.length = ds.length := by
                    intro ds; induction' ds using List.reverseRecOn with ds ih <;> aesop;
                  specialize h_contra ds a ha ; aesop;
                grind;
              aesop;
            · -- Since $j = \text{length}(ds)$, we have $s.data[j]! = a_1$ for some $a_1 \in ih$.
              obtain ⟨a, ha₁, a_1, ha₂, rfl⟩ := hs;
              have h_j_eq : j = ds.length := by
                linarith;
              -- Since $a$ is a string, its data is a list of characters. The length of $a$ is equal to the length of $ds$, so the $j$-th element of $a$'s data is the last character of $a$. But since $a$ is in the foldl result, which is built by appending characters, the last character of $a$ must be $a_1$. Therefore, the $j$-th element of $a$'s data is $a_1$, which is in $ih$.
              have h_last_char : a.data.length = ds.length := by
                have h_last_char : ∀ (ds : List (List Char)), ∀ (s : String), s ∈ List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) [""] ds → s.data.length = ds.length := by
                  intros ds s hs; induction' ds using List.reverseRecOn with ds ih generalizing s <;> simp_all +decide [ List.getElem?_append ] ;
                  rcases hs with ⟨ a, ha₁, a_2, ha₂, rfl ⟩ ; simp +decide [ *, String.data_append ];
                exact h_last_char ds a ha₁;
              simp +decide [ h_j_eq, h_last_char, String.data ];
              assumption;
          -- Apply the h_comb lemma with the appropriate parameters.
          specialize h_comb (List.map VerinaSpec.digitToLetters digits.data) (result[i]) (hp_1 _ (by
          grind)) j (by
          simpa using hj);
          cases h : digits.data[j]? <;> aesop;
        · -- By definition of `letterCombinations`, the result is a list of unique combinations.
          have h_unique : List.Nodup (List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) [""] (List.map VerinaSpec.digitToLetters digits.data)) := by
            have h_unique : ∀ (ds : List Char), (∀ d ∈ ds, VerinaSpec.digitToLetters d ≠ []) → List.Nodup (List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) [""] (List.map VerinaSpec.digitToLetters ds)) := by
              intro ds hds; induction' ds using List.reverseRecOn with ds ih <;> simp_all +decide [ List.foldl ] ;
              rw [ List.nodup_flatMap ];
              -- Since the original list is nodup and the function being mapped is injective, the resulting list is also nodup.
              have h_nodup : ∀ (s : String), List.Nodup (List.map (fun c => s ++ String.singleton c) (VerinaSpec.digitToLetters ih)) := by
                intro s; rw [ List.nodup_map_iff_inj_on ] ;
                · simp +decide [ String.ext_iff ];
                · unfold VerinaSpec.digitToLetters; aesop;
              refine' ⟨ fun s hs => h_nodup s, _ ⟩;
              -- Since the original list is nodup, any two different elements in the list will have different prefixes. The function being applied is appending a character from the digitToLetters of ih. Since the digitToLetters of ih are distinct, appending different characters to different prefixes will result in distinct strings. Therefore, the pairwise disjointness holds.
              have h_disjoint : ∀ (s t : String), s ≠ t → List.Disjoint (List.map (fun c => s ++ String.singleton c) (VerinaSpec.digitToLetters ih)) (List.map (fun c => t ++ String.singleton c) (VerinaSpec.digitToLetters ih)) := by
                intros s t hst; rw [ List.disjoint_left ] ; simp +decide [ hst ] ;
                intro a ha x hx; contrapose! hst; simp_all +decide [ String.ext_iff ] ;
                replace hst := congr_arg List.dropLast hst ; aesop;
              exact List.Pairwise.imp_of_mem ( by aesop ) ‹List.Nodup ( List.foldl ( fun ( acc : List String ) ( ls : List Char ) => List.flatMap ( fun ( s : String ) => List.map ( fun ( c : Char ) => s ++ String.singleton c ) ls ) acc ) [ "" ] ( List.map VerinaSpec.digitToLetters ds ) ) ›;
            apply h_unique;
            -- Since `LeetProofSpec.isValidDigit d` is true, `VerinaSpec.digitToLetters d` cannot be empty.
            intros d hd
            have h_valid : LeetProofSpec.isValidDigit d := h d hd
            simp [LeetProofSpec.isValidDigit] at h_valid;
            exact ne_of_apply_ne List.length h_valid.ne';
          have h_unique : List.toFinset result = List.toFinset (List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) [""] (List.map VerinaSpec.digitToLetters digits.data)) := by
            ext x; aesop;
          rw [ List.nodup_iff_injective_get ];
          intro i j hij;
          have := Finset.card_image_iff.mp ( show Finset.card ( Finset.image ( fun x : Fin result.length => result.get x ) Finset.univ ) = Finset.card ( Finset.univ : Finset ( Fin result.length ) ) from ?_ ) ; aesop;
          rw [ show ( Finset.image ( fun x : Fin result.length => result.get x ) Finset.univ ) = result.toFinset from ?_, h_unique ];
          · rw [ List.toFinset_card_of_nodup ] <;> aesop;
          · exact?;
        · intro combo hcombo hcombo'; convert hq _ _;
          have h_foldl : ∀ (ds : List Char), (∀ c ∈ ds, c ∈ ['2', '3', '4', '5', '6', '7', '8', '9']) → ∀ (combo : List Char), combo.length = ds.length → (∀ j < ds.length, combo[j]! ∈ VerinaSpec.digitToLetters (ds[j]!)) → combo.asString ∈ List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) [""] (List.map VerinaSpec.digitToLetters ds) := by
            intros ds hds combo hcombo hcombo'; induction' ds with d ds ih generalizing combo <;> simp_all +decide [ List.foldl ] ;
            rcases combo with ( _ | ⟨ c, combo ⟩ ) <;> simp_all +decide [ List.get ];
            · cases hcombo;
            · specialize ih combo ( by simpa using hcombo ) ( fun j hj => hcombo' ( j + 1 ) ( by linarith ) ) ; simp_all +decide [ List.asString ] ;
              have h_foldl : ∀ (ds : List Char), (∀ c ∈ ds, c ∈ ['2', '3', '4', '5', '6', '7', '8', '9']) → ∀ (ls : List Char), (∀ c ∈ ls, c ∈ VerinaSpec.digitToLetters d) → ∀ (combo : String), combo ∈ List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) [""] (List.map VerinaSpec.digitToLetters ds) → ∀ (c : Char), c ∈ ls → String.singleton c ++ combo ∈ List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) (List.map (fun (c : Char) => String.singleton c) ls) (List.map VerinaSpec.digitToLetters ds) := by
                intros ds hds ls hls combo hcombo c hc; induction' ds using List.reverseRecOn with d ds ih generalizing combo <;> simp_all +decide [ List.foldl ] ;
                · exact ⟨ c, hc, rfl ⟩;
                · rcases hcombo with ⟨ a, ha, b, hb, rfl ⟩ ; exact ⟨ _, ih _ ha, _, hb, by simp +decide [ String.ext_iff ] ⟩ ;
              convert h_foldl ds ( by aesop ) ( VerinaSpec.digitToLetters d ) ( by aesop ) _ ih _ _ using 1;
              simpa using hcombo' 0 ( Nat.zero_lt_succ _ );
          convert h_foldl digits.data _ combo _ _;
          · grind;
          · exact hcombo;
          · intro j hj;
            convert hcombo' j ( by simpa using hj ) using 1;
            · cases h : digits.data[j]? <;> aesop;
            · exact?;
  · intro h_postcond
    simp [VerinaSpec.letterCombinations_postcond] at *;
    split_ifs <;> simp_all +decide [ LeetProofSpec.postcondition ];
    · -- If there exists a character in the digits that is not a valid digit, then allValidDigits digits must be false.
      have h_allValidDigits_false : ¬LeetProofSpec.allValidDigits digits := by
        -- If there exists a character in the digits that is not a valid digit, then allValidDigits digits must be false because the allValidDigits function checks if all characters in the string are valid digits.
        simp [LeetProofSpec.allValidDigits] at *;
        obtain ⟨ x, hx₁, hx₂ ⟩ := ‹∃ x ∈ digits.data, _›; use x; simp_all +decide [ LeetProofSpec.isValidDigit ] ;
        unfold LeetProofSpec.digitToLetters; aesop;
      grind;
    · -- Let's simplify the goal using the fact that `digits` is non-empty and all its digits are valid.
      have h_all_valid : LeetProofSpec.allValidDigits digits = Bool.true := by
        -- Since every character in `digits.data` is one of 2, 3, 4, 5, 6, 7, 8, or 9, each character is valid.
        have h_valid : ∀ c ∈ digits.data, LeetProofSpec.isValidDigit c := by
          -- Since every character in `digits.data` is one of 2, 3, 4, 5, 6, 7, 8, or 9, each character is valid by definition.
          intros c hc
          have h_char : c = '2' ∨ c = '3' ∨ c = '4' ∨ c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9' := by
            grind;
          rcases h_char with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> trivial;
        unfold LeetProofSpec.allValidDigits; aesop;
      -- By definition of `digitToLetters`, we know that the foldl result is exactly the set of all valid combinations.
      have h_foldl_eq_combinations : List.foldl (fun (acc : List String) (ls : List Char) => List.flatMap (fun (s : String) => List.map (fun (c : Char) => s ++ String.singleton c) ls) acc) [""] (List.map VerinaSpec.digitToLetters digits.data) = List.map (fun (combo : List Char) => combo.asString) (List.foldl (fun (acc : List (List Char)) (ls : List Char) => List.flatMap (fun (combo : List Char) => List.map (fun (c : Char) => combo ++ [c]) ls) acc) [[]] (List.map (fun (c : Char) => LeetProofSpec.digitToLetters c) digits.data)) := by
        induction' digits.data using List.reverseRecOn with digits ih <;> simp_all +decide [ List.foldl ];
        induction ( List.foldl ( fun ( acc : List ( List Char ) ) ( ls : List Char ) => List.flatMap ( fun ( combo : List Char ) => List.map ( fun ( c : Char ) => combo ++ [ c ] ) ls ) acc ) [ [ ] ] ( List.map ( fun ( c : Char ) => LeetProofSpec.digitToLetters c ) digits ) ) <;> simp +decide [ * ];
        unfold VerinaSpec.digitToLetters LeetProofSpec.digitToLetters; aesop;
      -- By definition of `foldl`, the length of the foldl result is the product of the lengths of the digitToLetters lists.
      have h_foldl_length : (List.foldl (fun (acc : List (List Char)) (ls : List Char) => List.flatMap (fun (combo : List Char) => List.map (fun (c : Char) => combo ++ [c]) ls) acc) [[]] (List.map (fun (c : Char) => LeetProofSpec.digitToLetters c) digits.data)).length = List.prod (List.map (fun (c : Char) => (LeetProofSpec.digitToLetters c).length) digits.data) := by
        induction' digits.data using List.reverseRecOn with c cs ih <;> simp_all +decide [ List.prod_cons ];
      simp_all +decide [ List.mem_map ];
      refine' ⟨ _, _, _ ⟩;
      · exact?;
      · intro x hx;
        have h_exists_combination : ∀ x ∈ result, ∃ combo : List Char, combo.length = digits.length ∧ (∀ j : ℕ, j < digits.length → combo[j]! ∈ LeetProofSpec.digitToLetters (digits.data[j]!)) ∧ combo.asString = x := by
          intro x hx
          obtain ⟨i, hi⟩ : ∃ i : ℕ, i < result.length ∧ result[i]! = x := by
            obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hx;
            exact ⟨ i, i.2, by simpa [ Fin.cast_val_eq_self ] using hi ⟩;
          aesop;
        obtain ⟨ combo, hcombo₁, hcombo₂, rfl ⟩ := h_exists_combination x hx;
        -- By definition of `digitToLetters`, each element in the foldl result is a combination of letters from the digitToLetters lists.
        have h_foldl_combinations : ∀ (ds : List Char), (∀ d ∈ ds, LeetProofSpec.isValidDigit d) → ∀ (combo : List Char), combo.length = ds.length → (∀ j : ℕ, j < ds.length → combo[j]! ∈ LeetProofSpec.digitToLetters ds[j]!) → combo ∈ List.foldl (fun (acc : List (List Char)) (ls : List Char) => List.flatMap (fun (combo : List Char) => List.map (fun (c : Char) => combo ++ [c]) ls) acc) [[]] (List.map (fun (c : Char) => LeetProofSpec.digitToLetters c) ds) := by
          -- We'll use induction on the list `ds`.
          intro ds hds combo hcombo₁ hcombo₂
          induction' ds with d ds ih generalizing combo;
          · cases combo <;> trivial;
          · rcases combo with ( _ | ⟨ c, combo ⟩ ) <;> simp_all +decide [ List.length ];
            specialize ih combo hcombo₁ ( fun j hj => hcombo₂ ( j + 1 ) ( by linarith ) ) ; simp_all +decide [ List.foldl ] ;
            have h_foldl_combinations : ∀ (ds : List Char), (∀ d ∈ ds, LeetProofSpec.isValidDigit d) → ∀ (combo : List Char), combo ∈ List.foldl (fun (acc : List (List Char)) (ls : List Char) => List.flatMap (fun (combo : List Char) => List.map (fun (c : Char) => combo ++ [c]) ls) acc) [[]] (List.map (fun (c : Char) => LeetProofSpec.digitToLetters c) ds) → ∀ (c : Char), c ∈ LeetProofSpec.digitToLetters d → c :: combo ∈ List.foldl (fun (acc : List (List Char)) (ls : List Char) => List.flatMap (fun (combo : List Char) => List.map (fun (c : Char) => combo ++ [c]) ls) acc) (List.map (fun (c : Char) => [c]) (LeetProofSpec.digitToLetters d)) (List.map (fun (c : Char) => LeetProofSpec.digitToLetters c) ds) := by
              intros ds hds combo hcombo c hc; induction' ds using List.reverseRecOn with d ds ih generalizing combo c <;> simp_all +decide [ List.foldl ] ;
              grind +ring;
            exact h_foldl_combinations ds ( fun x hx => by
              exact hds.2 x hx ) combo ih c ( by
              simpa using hcombo₂ 0 ( Nat.zero_lt_succ _ ) );
        exact ⟨ combo, h_foldl_combinations digits.data ( by
          unfold LeetProofSpec.allValidDigits at h_all_valid; aesop; ) combo hcombo₁ hcombo₂, rfl ⟩;
      · -- By definition of `foldl`, each element in the foldl result is a valid combination of the digits.
        have h_valid_combinations : ∀ a ∈ List.foldl (fun (acc : List (List Char)) (ls : List Char) => List.flatMap (fun (combo : List Char) => List.map (fun (c : Char) => combo ++ [c]) ls) acc) [[]] (List.map (fun (c : Char) => LeetProofSpec.digitToLetters c) digits.data), a.length = digits.length ∧ (∀ j < digits.length, a[j]! ∈ LeetProofSpec.digitToLetters (digits.data[j]!)) := by
          have h_valid_combinations : ∀ (ds : List (List Char)), (∀ a ∈ List.foldl (fun (acc : List (List Char)) (ls : List Char) => List.flatMap (fun (combo : List Char) => List.map (fun (c : Char) => combo ++ [c]) ls) acc) [[]] ds, a.length = ds.length ∧ (∀ j < ds.length, a[j]! ∈ ds[j]!)) := by
            intro ds; induction' ds using List.reverseRecOn with ds ih <;> simp_all +decide ;
            grind;
          convert h_valid_combinations ( List.map ( fun c => LeetProofSpec.digitToLetters c ) digits.data ) using 1;
          simp +decide [ List.getElem?_eq_getElem ];
          congr! 3;
          cases h : digits.data[‹_›]? <;> simp +decide [ h ];
          · simp_all +decide [ List.getElem?_eq_none ];
            exact fun h' => False.elim <| h'.not_le h;
          · rfl;
        intro a ha; specialize h_valid_combinations a ha; aesop;