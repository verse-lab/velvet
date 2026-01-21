/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b2068e9e-d91d-4a52-bd47-bab5e9895a6a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : List Int):
  VerinaSpec.uniqueSorted_precond arr ↔ LeetProofSpec.precondition arr

- theorem postcondition_equiv (arr : List Int) (result : List Int) (h_precond : VerinaSpec.uniqueSorted_precond arr):
  VerinaSpec.uniqueSorted_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def uniqueSorted_precond (arr : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def uniqueSorted_postcond (arr : List Int) (result: List Int) (h_precond : uniqueSorted_precond (arr)) : Prop :=
  -- !benchmark @start postcond
  List.isPerm arr.eraseDups result ∧ List.Pairwise (· ≤ ·) result

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if a list is sorted in ascending order
def isSortedAsc (lst : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < lst.length → lst[i]! ≤ lst[j]!

-- Helper: Check if a list has no duplicates (all elements are distinct)
def hasNoDuplicates (lst : List Int) : Prop :=
  ∀ i j : Nat, i < lst.length → j < lst.length → i ≠ j → lst[i]! ≠ lst[j]!

-- Postcondition clause 1: result is sorted in ascending order
def ensures1 (arr : List Int) (result : List Int) :=
  isSortedAsc result

-- Postcondition clause 2: result has no duplicates
def ensures2 (arr : List Int) (result : List Int) :=
  hasNoDuplicates result

-- Postcondition clause 3: membership preservation (element is in result iff it's in arr)
def ensures3 (arr : List Int) (result : List Int) :=
  ∀ x : Int, x ∈ result ↔ x ∈ arr

def precondition (arr : List Int) :=
  True

-- no preconditions

def postcondition (arr : List Int) (result : List Int) :=
  ensures1 arr result ∧ ensures2 arr result ∧ ensures3 arr result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : List Int):
  VerinaSpec.uniqueSorted_precond arr ↔ LeetProofSpec.precondition arr := by
  tauto

theorem postcondition_equiv (arr : List Int) (result : List Int) (h_precond : VerinaSpec.uniqueSorted_precond arr):
  VerinaSpec.uniqueSorted_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result := by
  constructor;
  · -- If the result is a permutation of the original array and is sorted, then it satisfies the LeetProofSpec's postcondition.
    intro h_perm_sorted
    have h_sorted : LeetProofSpec.ensures1 arr result := by
      cases h_perm_sorted;
      intro i j hij hj;
      have := List.pairwise_iff_get.mp ‹_›;
      convert this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij;
      · grind;
      · grind
    have h_no_duplicates : LeetProofSpec.ensures2 arr result := by
      obtain ⟨ h_perm, h_sorted ⟩ := h_perm_sorted;
      -- Since result is a permutation of arr.eraseDups, and arr.eraseDups has no duplicates, result must also have no duplicates.
      have h_no_duplicates : List.Nodup result := by
        have h_no_duplicates : List.Nodup (arr.eraseDups) := by
          -- By definition of `List.eraseDupsBy.loop`, it ensures that the resulting list has no duplicates.
          have h_eraseDupsBy_loop : ∀ {l : List ℤ} {acc : List ℤ}, List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun (x1 x2 : ℤ) => x1 == x2) l acc) := by
            intros l acc hacc; induction' l with x l ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
            cases h : acc.any fun x2 => x == x2 <;> aesop;
          exact h_eraseDupsBy_loop ( by simp +decide );
        -- Since permutations preserve the nodup property, if arr.eraseDups is nodup, then result must also be nodup.
        have h_perm_nodup : ∀ {l1 l2 : List ℤ}, List.Perm l1 l2 → List.Nodup l1 → List.Nodup l2 := by
          exact?;
        exact h_perm_nodup ( by simpa [ List.isPerm_iff ] using h_perm ) h_no_duplicates;
      intro i j hi hj hij; have := List.nodup_iff_injective_get.mp h_no_duplicates; have := @this ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; aesop;
    have h_elements : LeetProofSpec.ensures3 arr result := by
      -- Since `result` is a permutation of `arr`, every element in `result` is in `arr` and vice versa.
      have h_perm : ∀ x, x ∈ result ↔ x ∈ arr := by
        have h_perm_def : List.isPerm arr.eraseDups result := h_perm_sorted.left
        have h_perm_def : ∀ x, x ∈ arr.eraseDups ↔ x ∈ arr := by
          -- By definition of `List.eraseDupsBy.loop`, if `x` is in the list after `eraseDupsBy.loop`, then `x` must have been in the original list.
          have h_eraseDupsBy_loop : ∀ (l : List ℤ) (acc : List ℤ), (∀ x, x ∈ List.eraseDupsBy.loop (fun x y => decide (x == y)) l acc ↔ x ∈ l ∨ x ∈ acc) := by
            intros l acc x; induction' l with hd tl ih generalizing acc <;> simp +decide [ List.eraseDupsBy.loop ] ;
            by_cases h : hd ∈ acc <;> simp_all +decide [ List.any_eq ];
            · grind;
            · tauto;
          exact fun x => by simpa using h_eraseDupsBy_loop arr [] x;
        -- Since `arr.eraseDups` is a permutation of `result`, for any `x`, `x ∈ arr.eraseDups` implies `x ∈ result` and vice versa.
        have h_perm_elements : ∀ x, x ∈ arr.eraseDups ↔ x ∈ result := by
          -- Since `arr.eraseDups` is a permutation of `result`, they have the same elements.
          have h_perm_elements : List.Perm (arr.eraseDups) result := by
            exact?;
          exact fun x => h_perm_elements.mem_iff;
        aesop;
      exact h_perm
    exact ⟨h_sorted, h_no_duplicates, h_elements⟩;
  · intro h_postcond;
    -- To prove the permutation part, we can use the fact that if two lists have the same elements and are sorted, they must be permutations of each other.
    have h_perm : List.Perm result arr.eraseDups := by
      -- Since result is sorted and has no duplicates, it must be a sorted list of the unique elements of arr.
      have h_unique_elements : List.toFinset result = List.toFinset (arr.eraseDups) := by
        -- By definition of `arr.eraseDups`, the elements of `arr.eraseDups` are exactly the elements of `arr` that appear exactly once.
        have h_eraseDups : List.toFinset (arr.eraseDups) = List.toFinset arr := by
          ext x;
          simp +decide [ List.mem_toFinset ];
          -- By definition of `List.eraseDupsBy.loop`, it preserves the elements of the list.
          have h_loop : ∀ (l : List ℤ) (acc : List ℤ), x ∈ List.eraseDupsBy.loop (· == ·) l acc ↔ x ∈ l ∨ x ∈ acc := by
            intros l acc; induction' l with hd tl ih generalizing acc <;> simp +decide [ List.eraseDupsBy.loop ] ; aesop;
          simpa using h_loop arr [ ];
        ext x; have := h_postcond.2.2 x; aesop;
      rw [ List.perm_iff_count ];
      intro x; by_cases hx : x ∈ result <;> by_cases hx' : x ∈ arr.eraseDups <;> simp_all +decide [ Finset.ext_iff ] ;
      · rw [ List.count_eq_one_of_mem, List.count_eq_one_of_mem ];
        · -- By definition of `eraseDupsBy.loop`, the resulting list is nodup.
          have h_loop_nodup : ∀ (l : List ℤ) (acc : List ℤ), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
            intros l acc hacc; induction' l with hd tl ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
            by_cases h : acc.any fun x2 => hd == x2 <;> simp +decide [ h, ih, hacc ];
            exact ih _ ( by aesop );
          exact h_loop_nodup _ _ ( by simp +decide );
        · assumption;
        · have := h_postcond.2.1;
          rw [ List.nodup_iff_injective_get ];
          intro i j hij; have := this i j; aesop;
        · grind;
      · rw [ List.count_eq_zero_of_not_mem, List.count_eq_zero_of_not_mem ] <;> aesop;
    constructor;
    · exact?;
    · have := h_postcond.1;
      rw [ List.pairwise_iff_get ];
      intro i j hij; have := this i j; aesop;
