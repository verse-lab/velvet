/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 68ac74fd-7864-4a23-9e5f-620315392e20

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Int):
  VerinaSpec.findProduct_precond lst ↔ LeetProofSpec.precondition lst

- theorem postcondition_equiv (lst : List Int) (result : Int) (h_precond : VerinaSpec.findProduct_precond lst):
  VerinaSpec.findProduct_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none

def findProduct_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)

-- !benchmark @end precond

def findProduct_postcond (lst : List Int) (result: Int) (h_precond : findProduct_precond (lst)) :=
  -- !benchmark @start postcond
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Check if an integer is even
def isEven (n : Int) : Prop := n % 2 = 0

-- Check if an integer is odd
def isOdd (n : Int) : Prop := n % 2 ≠ 0

-- Predicate: element at index i is the first even number in the list
def isFirstEvenAt (lst : List Int) (i : Nat) : Prop :=
  i < lst.length ∧
  isEven lst[i]! ∧
  ∀ j : Nat, j < i → ¬isEven lst[j]!

-- Predicate: element at index i is the first odd number in the list
def isFirstOddAt (lst : List Int) (i : Nat) : Prop :=
  i < lst.length ∧
  isOdd lst[i]! ∧
  ∀ j : Nat, j < i → ¬isOdd lst[j]!

-- Precondition: list contains at least one even and at least one odd number
def require1 (lst : List Int) : Prop :=
  ∃ x ∈ lst, isEven x

def require2 (lst : List Int) : Prop :=
  ∃ x ∈ lst, isOdd x

-- Postcondition: result is product of first even and first odd
def ensures1 (lst : List Int) (result : Int) : Prop :=
  ∃ i j : Nat,
    isFirstEvenAt lst i ∧
    isFirstOddAt lst j ∧
    result = lst[i]! * lst[j]!

def precondition (lst : List Int) : Prop :=
  require1 lst ∧ require2 lst

def postcondition (lst : List Int) (result : Int) : Prop :=
  ensures1 lst result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (lst : List Int):
  VerinaSpec.findProduct_precond lst ↔ LeetProofSpec.precondition lst := by
  -- The length condition in VerinaSpec is redundant because if there's at least one even and one odd, the list must have at least two elements.
  simp [VerinaSpec.findProduct_precond, LeetProofSpec.precondition];
  unfold LeetProofSpec.require1 LeetProofSpec.require2;
  unfold LeetProofSpec.isEven LeetProofSpec.isOdd
  simp [VerinaSpec.isEven, VerinaSpec.isOdd] at *;
  intro x hx hx' y hy hy'; contrapose! hy'; rcases lst with ( _ | ⟨ _, _ | ⟨ _, _ | lst ⟩ ⟩ ) <;> aesop;

theorem postcondition_equiv (lst : List Int) (result : Int) (h_precond : VerinaSpec.findProduct_precond lst):
  VerinaSpec.findProduct_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result := by
  -- By definition of equivalence, if two propositions are equivalent, then their postconditions are also equivalent. We can split the equivalence into two implications.
  apply Iff.intro;
  · -- By definition of `firstEvenOddIndices`, if it returns some indices, then those indices are indeed the first even and first odd in the list.
    obtain ⟨ei, oi, h_indices⟩ : ∃ ei oi, VerinaSpec.firstEvenOddIndices lst = some (ei, oi) := by
      -- By definition of `findProduct_precond`, if `list.length > 1` and there exist even and odd numbers in the list, then `firstEvenOddIndices` must return some indices.
      have h_even_odd : ∃ x ∈ lst, VerinaSpec.isEven x ∧ ∃ y ∈ lst, VerinaSpec.isOdd y := by
        unfold VerinaSpec.findProduct_precond at h_precond; aesop;
      -- Since the list is non-empty and contains both even and odd numbers, the findIdx? function will return some indices for both even and odd numbers.
      have h_even_odd_indices : ∃ ei oi, List.findIdx? VerinaSpec.isEven lst = some ei ∧ List.findIdx? VerinaSpec.isOdd lst = some oi := by
        cases h : List.findIdx? VerinaSpec.isEven lst <;> cases h' : List.findIdx? VerinaSpec.isOdd lst <;> aesop;
      unfold VerinaSpec.firstEvenOddIndices; aesop;
    -- By definition of `findIdx?`, if `findIdx? isEven` returns `some ei`, then `ei` is the first index where `isEven` holds.
    have h_even : List.findIdx? (fun (a : ℤ) => a % 2 = 0) lst = some ei := by
      unfold VerinaSpec.firstEvenOddIndices at h_indices;
      unfold VerinaSpec.isEven at h_indices; aesop;
    have h_odd : List.findIdx? (fun (a : ℤ) => a % 2 ≠ 0) lst = some oi := by
      unfold VerinaSpec.firstEvenOddIndices at h_indices;
      unfold VerinaSpec.isEven VerinaSpec.isOdd at * ; aesop;
    have h_even : ∀ j, j < ei → ¬(lst[j]! % 2 = 0) := by
      intro j hj;
      have h_even : ∀ {l : List ℤ} {p : ℤ → Bool} {i : ℕ}, List.findIdx? p l = some i → ∀ j, j < i → ¬p (l[j]!) := by
        intros l p i hi j hj; induction' l with hd tl ih generalizing i j; aesop;
        rcases i with ( _ | i ) <;> simp_all +decide [ List.findIdx?_cons ];
        cases j <;> aesop;
      specialize h_even ‹_› j hj; aesop;
    have h_odd : ∀ j, j < oi → ¬(lst[j]! % 2 ≠ 0) := by
      have h_odd : ∀ {l : List ℤ} {p : ℤ → Bool} {i : ℕ}, List.findIdx? p l = some i → ∀ j < i, ¬p (l[j]!) := by
        -- We'll use induction on the list to prove this.
        intro l p i hi
        induction' l with a l ih generalizing i;
        · cases hi;
        · rcases i with ( _ | i ) <;> simp_all +decide [ List.findIdx?_cons ];
          intro j hj; rcases j with ( _ | j ) <;> simp_all +decide ;
          · grind;
          · cases h : List.findIdx? p l <;> aesop;
      specialize @h_odd lst ( fun a => Decidable.decide ( a % 2 ≠ 0 ) ) oi ; aesop;
    have h_even : ei < lst.length ∧ lst[ei]! % 2 = 0 := by
      have h_even : ∀ {l : List ℤ} {p : ℤ → Bool} {i : ℕ}, List.findIdx? p l = some i → i < l.length ∧ p (l[i]!) := by
        -- We'll use induction on the list to prove this.
        intros l p i hi
        induction' l with a l ih generalizing i;
        · cases hi;
        · rw [ List.findIdx?_cons ] at hi ; aesop;
      grind
    have h_odd : oi < lst.length ∧ lst[oi]! % 2 ≠ 0 := by
      have h_findIdx : ∀ {l : List ℤ} {p : ℤ → Bool} {i : ℕ}, List.findIdx? p l = some i → i < l.length ∧ p (l[i]!) := by
        -- We can prove this by induction on the list.
        intros l p i hi
        induction' l with a l ih generalizing i;
        · cases hi;
        · rw [ List.findIdx?_cons ] at hi ; aesop;
      grind;
    exact fun h => ⟨ ei, oi, ⟨ h_even.1, h_even.2, by tauto ⟩, ⟨ h_odd.1, h_odd.2, by tauto ⟩, by unfold VerinaSpec.findProduct_postcond at h; aesop ⟩;
  · -- By definition of postcondition, if there exist indices i and j such that the element at i is the first even and the element at j is the first odd, then the result is their product.
    intro h_post
    obtain ⟨i, j, hi, hj, h_prod⟩ := h_post;
    -- By definition of `findIdx?`, we know that `lst.findIdx? isEven` returns the index of the first even number in `lst`, and `lst.findIdx? isOdd` returns the index of the first odd number in `lst`.
    have h_findIdx_even : lst.findIdx? (fun x => x % 2 = 0) = some i := by
      have h_findIdx_even : ∀ {i : ℕ} {l : List ℤ}, i < l.length → l[i]! % 2 = 0 → (∀ j < i, ¬l[j]! % 2 = 0) → List.findIdx? (fun x => x % 2 = 0) l = some i := by
        -- We proceed by induction on the list.
        intro i l hi hl h_ind
        induction' l with x l ih generalizing i;
        · contradiction;
        · rcases i with ( _ | i ) <;> simp_all +decide [ List.findIdx?_cons ];
          split_ifs <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
          · specialize h_ind 0 ; simp_all +decide [ Int.emod_eq_zero_of_dvd ];
          · exact ih hi hl fun j hj => h_ind ( j + 1 ) ( by linarith );
      exact h_findIdx_even hi.1 hi.2.1 hi.2.2
    have h_findIdx_odd : lst.findIdx? (fun x => x % 2 ≠ 0) = some j := by
      have h_findIdx_odd : ∀ {l : List ℤ} {j : ℕ}, j < l.length → (∀ k < j, ¬(l[k]! % 2 ≠ 0)) → (l[j]! % 2 ≠ 0) → List.findIdx? (fun x => x % 2 ≠ 0) l = some j := by
        -- We can prove this by induction on the list.
        intro l j hj h_not_odd h_odd
        induction' l with x l ih generalizing j;
        · contradiction;
        · rcases j with ( _ | j ) <;> simp_all +decide [ List.findIdx?_cons ];
          rw [ if_neg ( by specialize h_not_odd 0; aesop ) ];
          rw [ ih hj ( fun k hk => by simpa using h_not_odd ( k + 1 ) ( by linarith ) ) h_odd ] ; aesop;
      -- Apply the h_findIdx_odd lemma with the given hypotheses.
      apply h_findIdx_odd hj.1 hj.2.2 hj.2.1;
    -- By definition of `findProduct_postcond`, we need to show that if `lst.findIdx? isEven = some i` and `lst.findIdx? isOdd = some j`, then `result = lst[i]! * lst[j]!`.
    simp [VerinaSpec.findProduct_postcond, h_findIdx_even, h_findIdx_odd];
    rw [ VerinaSpec.firstEvenOddIndices ];
    unfold VerinaSpec.isEven VerinaSpec.isOdd; aesop;