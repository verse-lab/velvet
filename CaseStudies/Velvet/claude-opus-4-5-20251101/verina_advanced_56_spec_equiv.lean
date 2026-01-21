/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c3d68bd4-b19e-41d6-bf64-fc435d886509

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int):
  VerinaSpec.moveZeroes_precond xs ↔ LeetProofSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : List Int) (h_precond : VerinaSpec.moveZeroes_precond xs):
  VerinaSpec.moveZeroes_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def moveZeroes_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

-- Count how many times a specific value appears in the list

def countVal (val : Int) : List Int → Nat
  | [] => 0
  | x :: xs =>
    let rest := countVal val xs
    if x = val then rest + 1 else rest

-- Check whether one list is a subsequence of another (preserving relative order)
def isSubsequence (xs ys : List Int) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
    if x = y then isSubsequence xt yt else isSubsequence xs yt

@[reducible]
def moveZeroes_postcond (xs : List Int) (result: List Int) (h_precond : moveZeroes_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  -- 1. All non-zero elements must maintain their relative order
  isSubsequence (xs.filter (fun x => x ≠ 0)) result = true ∧

  -- 2. All zeroes must be located at the end of the output list
  (result.dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) ∧

  -- 3. The output must contain the same number of elements,
  --    and the number of zeroes must remain unchanged
  countVal 0 xs = countVal 0 result ∧
  xs.length = result.length

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Get non-zero elements preserving order (used for specifying relative order preservation)
def nonZeroElements (xs : List Int) : List Int :=
  xs.filter (· ≠ 0)

-- Postcondition clauses

-- Every element appears the same number of times in result as in input (implies same length)
def ensures1 (xs : List Int) (result : List Int) :=
  ∀ x : Int, result.count x = xs.count x

-- All non-zero elements come before all zero elements
-- If position i has a zero and position j > i, then position j must also have a zero
def ensures2 (xs : List Int) (result : List Int) :=
  ∀ i j : Nat, i < j → j < result.length → result[i]! = 0 → result[j]! = 0

-- The non-zero elements in the result preserve their relative order from input
-- This is captured by: the subsequence of non-zeros in result equals the subsequence of non-zeros in input
def ensures3 (xs : List Int) (result : List Int) :=
  nonZeroElements result = nonZeroElements xs

def precondition (xs : List Int) :=
  True

-- no preconditions

def postcondition (xs : List Int) (result : List Int) :=
  ensures1 xs result ∧ ensures2 xs result ∧ ensures3 xs result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (xs : List Int):
  VerinaSpec.moveZeroes_precond xs ↔ LeetProofSpec.precondition xs := by
  exact iff_of_true trivial trivial

noncomputable section AristotleLemmas

theorem VerinaSpec.countVal_eq_count (val : Int) (xs : List Int) :
  VerinaSpec.countVal val xs = xs.count val := by
    induction xs <;> simp +decide [ *, List.count ];
    · rfl;
    · simp_all +decide [ VerinaSpec.countVal, List.countP_cons ];
      grind

theorem VerinaSpec.isSubsequence_iff_sublist (xs ys : List Int) :
  VerinaSpec.isSubsequence xs ys = true ↔ List.Sublist xs ys := by
    induction' xs with x xs ih generalizing ys <;> induction' ys with y ys ih' <;> simp +decide [ *, List.sublist_cons_iff ];
    · rfl;
    · rfl;
    · by_cases h : x = y <;> simp_all +decide [ VerinaSpec.isSubsequence ];
      grind

theorem VerinaSpec.dropWhile_all_zero_iff (l : List Int) :
  (l.dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) ↔
  ∀ i j : Nat, i < j → j < l.length → l[i]! = 0 → l[j]! = 0 := by
    constructor;
    · intro h i j hij hj hl_i_zero
      have hl_j_zero : l[j]! ∈ List.dropWhile (fun x => x ≠ 0) l := by
        have h_j_in_dropWhile : ∀ {xs : List ℤ}, l = xs → j < xs.length → xs[j]! = 0 → xs[j]! ∈ List.dropWhile (fun x => x ≠ 0) xs := by
          intros xs hxs hj hl_j_zero
          induction' xs with x xs ih generalizing j;
          · contradiction;
          · by_cases hx : x = 0 <;> simp_all +decide [ List.dropWhile ];
            have h_dropWhile : ∀ {xs : List ℤ}, (∃ j, j < xs.length ∧ xs[j]! = 0) → 0 ∈ List.dropWhile (fun x => !Decidable.decide (x = 0)) xs := by
              intros xs hxs; induction' xs with x xs ih <;> simp_all +decide [ List.dropWhile ] ;
              rcases hxs with ⟨ j, hj₁, hj₂ ⟩ ; rcases j with ( _ | j ) <;> simp_all +decide [ List.getElem?_cons ] ;
              by_cases hx : x = 0 <;> simp_all +decide [ List.dropWhile ];
              exact ih _ hj₁ hj₂;
            grind;
        apply h_j_in_dropWhile rfl hj;
        have h_all_zero : ∀ {xs : List ℤ}, (List.dropWhile (fun x => x ≠ 0) xs).all (fun x => x = 0) → ∀ {i : ℕ}, i < xs.length → xs[i]! = 0 → ∀ {j : ℕ}, i < j → j < xs.length → xs[j]! = 0 := by
          intros xs hxs i hi hi_zero j hij hj_zero
          induction' xs with x xs ih generalizing i j;
          · contradiction;
          · rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide;
            by_cases hx : x = 0 <;> simp_all +decide [ List.dropWhile ];
            · exact hxs _ ( by simp );
            · exact ih hxs hi hi_zero hij hj_zero;
        exact h_all_zero h ( show i < l.length from lt_of_lt_of_le hij ( Nat.le_of_lt hj ) ) hl_i_zero hij hj;
      grind;
    · intro h;
      induction' l with x l ih;
      · rfl;
      · by_cases hx : x ≠ 0 <;> simp_all +decide;
        · convert ih _ using 1;
          intro i j hij hj; specialize h ( i + 1 ) ( j + 1 ) ( by linarith ) ( by linarith ) ; aesop;
        · -- By the hypothesis h, if i < j and l[j] is zero, then l[i] must also be zero.
          have h_zero : ∀ i : ℕ, i < l.length → l[i]? = some 0 := by
            intro i hi; specialize h 0 ( i + 1 ) ; aesop;
          intro x hx; obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hx; specialize h_zero i; aesop;

theorem VerinaSpec.length_filter_neq_zero (l : List Int) :
  (l.filter (fun x => x ≠ 0)).length + l.count 0 = l.length := by
    -- We can prove this by induction on the list `l`.
    induction' l with x l ih;
    · rfl;
    · grind

theorem VerinaSpec.ensures1_implies_counts_and_length (xs result : List Int) :
  LeetProofSpec.ensures1 xs result →
  VerinaSpec.countVal 0 xs = VerinaSpec.countVal 0 result ∧ xs.length = result.length := by
    intro h;
    -- Apply `VerinaSpec.countVal_eq_count` to rewrite the counts in terms of `List.count`.
    have h_count_0 : VerinaSpec.countVal 0 xs = xs.count 0 ∧ VerinaSpec.countVal 0 result = result.count 0 := by
      exact ⟨ VerinaSpec.countVal_eq_count 0 xs, VerinaSpec.countVal_eq_count 0 result ⟩;
    -- By definition of `List.Perm`, we know that `xs.count x = result.count x` for all `x` implies `xs ~ result`.
    have h_perm : ∀ x, List.count x xs = List.count x result := by
      exact fun x => h x ▸ rfl;
    exact ⟨ h_count_0.1.trans ( h_perm 0 |> Eq.trans <| h_count_0.2.symm ), by simpa using List.Perm.length_eq <| List.perm_iff_count.mpr h_perm ⟩

end AristotleLemmas

theorem postcondition_equiv (xs : List Int) (result : List Int) (h_precond : VerinaSpec.moveZeroes_precond xs):
  VerinaSpec.moveZeroes_postcond xs result h_precond ↔ LeetProofSpec.postcondition xs result := by
  constructor <;> intro h <;> constructor;
  · -- Apply the lemma ensures1_implies_counts_and_length to get the counts and lengths.
    have h_counts_and_length : VerinaSpec.countVal 0 xs = VerinaSpec.countVal 0 result ∧ (xs.length = result.length) := by
      exact ⟨ h.2.2.1, h.2.2.2 ⟩;
    intro x;
    -- Since `xs.filter (fun x => x ≠ 0)` is a sublist of `result` and they have the same length, they must be equal.
    have h_eq : xs.filter (fun x => x ≠ 0) = result.filter (fun x => x ≠ 0) := by
      have h_eq : List.Sublist (xs.filter (fun x => x ≠ 0)) result := by
        have h_eq : List.Sublist (xs.filter (fun x => x ≠ 0)) result := by
          have := h
          have := this.1;
          exact?;
        assumption;
      have h_eq_length : (xs.filter (fun x => x ≠ 0)).length = (result.filter (fun x => x ≠ 0)).length := by
        have h_eq_length : (xs.filter (fun x => x ≠ 0)).length + xs.count 0 = xs.length ∧ (result.filter (fun x => x ≠ 0)).length + result.count 0 = result.length := by
          have h_eq_length : ∀ l : List ℤ, (l.filter (fun x => x ≠ 0)).length + l.count 0 = l.length := by
            exact?;
          exact ⟨ h_eq_length xs, h_eq_length result ⟩;
        linarith [ show List.count 0 xs = List.count 0 result from by simpa [ VerinaSpec.countVal_eq_count ] using h_counts_and_length.1 ];
      have h_eq_elements : List.Sublist (xs.filter (fun x => x ≠ 0)) (result.filter (fun x => x ≠ 0)) := by
        have h_eq_elements : ∀ {l1 l2 : List ℤ}, List.Sublist l1 l2 → List.Sublist (List.filter (fun x => x ≠ 0) l1) (List.filter (fun x => x ≠ 0) l2) := by
          grind;
        convert h_eq_elements ‹_› using 1;
        norm_num [ List.filter_filter ];
      exact List.Sublist.eq_of_length_le h_eq_elements h_eq_length.ge;
    by_cases hx : x = 0 <;> simp_all +decide [ List.count_filter ];
    · -- Since `countVal` is equivalent to `List.count`, we can conclude that `List.count 0 xs = List.count 0 result`.
      have h_count_eq : List.count 0 xs = List.count 0 result := by
        have := h.2.2.1
        convert this using 1;
        · exact?;
        · exact?;
      exact h_count_eq.symm;
    · replace h_eq := congr_arg ( fun l => List.count x l ) h_eq ; aesop;
  · constructor;
    · convert VerinaSpec.dropWhile_all_zero_iff result |>.1 _ using 1;
      grind;
    · -- By definition of `isSubsequence`, we know that `xs.filter (fun x => x ≠ 0)` is a subsequence of `result`.
      have h_subseq : List.Sublist (xs.filter (fun x => x ≠ 0)) result := by
        exact VerinaSpec.isSubsequence_iff_sublist _ _ |>.1 h.1;
      -- Since `xs.filter (fun x => x ≠ 0)` is a subsequence of `result`, and `result` contains all the non-zero elements of `xs`, it follows that `xs.filter (fun x => x ≠ 0)` is equal to `result.filter (fun x => x ≠ 0)`.
      have h_eq : List.Sublist (xs.filter (fun x => x ≠ 0)) (result.filter (fun x => x ≠ 0)) := by
        have h_eq : ∀ {l1 l2 : List ℤ}, List.Sublist l1 l2 → List.Sublist (l1.filter (fun x => x ≠ 0)) (l2.filter (fun x => x ≠ 0)) := by
          grind;
        convert h_eq h_subseq using 1;
        exact Eq.symm ( by rw [ List.filter_filter ] ; aesop );
      have h_eq : List.length (xs.filter (fun x => x ≠ 0)) = List.length (result.filter (fun x => x ≠ 0)) := by
        have h_eq : List.length (xs.filter (fun x => x ≠ 0)) + List.count 0 xs = List.length xs ∧ List.length (result.filter (fun x => x ≠ 0)) + List.count 0 result = List.length result := by
          exact ⟨ by simpa using VerinaSpec.length_filter_neq_zero xs, by simpa using VerinaSpec.length_filter_neq_zero result ⟩;
        linarith [ h.2.2.1, h.2.2.2, show List.count 0 xs = List.count 0 result from by simpa [ VerinaSpec.countVal_eq_count ] using h.2.2.1 ];
      have h_eq : List.Sublist (xs.filter (fun x => x ≠ 0)) (result.filter (fun x => x ≠ 0)) ∧ List.length (xs.filter (fun x => x ≠ 0)) = List.length (result.filter (fun x => x ≠ 0)) → xs.filter (fun x => x ≠ 0) = result.filter (fun x => x ≠ 0) := by
        exact fun h => List.Sublist.eq_of_length_le h.1 h.2.ge;
      exact Eq.symm ( h_eq ⟨ by assumption, by assumption ⟩ );
  · -- By definition of `ensures3`, we know that `nonZeroElements result = nonZeroElements xs`.
    have h_nonzero_eq : List.filter (fun x => ¬x = 0) result = List.filter (fun x => ¬x = 0) xs := by
      exact h.2.2;
    rw [ ← h_nonzero_eq ];
    -- By definition of `isSubsequence`, we know that `List.filter (fun x => ¬x = 0) result` is a sublist of `result`.
    have h_sublist : List.Sublist (List.filter (fun x => ¬x = 0) result) result := by
      exact?;
    convert VerinaSpec.isSubsequence_iff_sublist _ _ |>.2 h_sublist using 1;
  · obtain ⟨h1, h2, h3⟩ := h;
    exact ⟨ by simpa using VerinaSpec.dropWhile_all_zero_iff result |>.2 fun i j hij hj => h2 i j hij hj, by simpa using VerinaSpec.ensures1_implies_counts_and_length xs result h1 ⟩