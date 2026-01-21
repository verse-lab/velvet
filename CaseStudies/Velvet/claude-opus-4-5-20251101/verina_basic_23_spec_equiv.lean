/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a7bce822-2e24-4534-9fd3-8c5c6c7d9a91

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int):
  VerinaSpec.differenceMinMax_precond a ↔ LeetProofSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.differenceMinMax_precond a):
  VerinaSpec.differenceMinMax_postcond a result h_precond ↔ LeetProofSpec.postcondition a result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def differenceMinMax_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0

-- !benchmark @end precond

def differenceMinMax_postcond (a : Array Int) (result: Int) (h_precond : differenceMinMax_precond (a)) :=
  -- !benchmark @start postcond
  result + (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)) = (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!))

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper definition: check if a value is the maximum in the array
def isMaximum (arr : Array Int) (val : Int) : Prop :=
  (∃ i : Nat, i < arr.size ∧ arr[i]! = val) ∧
  (∀ j : Nat, j < arr.size → arr[j]! ≤ val)

-- Helper definition: check if a value is the minimum in the array
def isMinimum (arr : Array Int) (val : Int) : Prop :=
  (∃ i : Nat, i < arr.size ∧ arr[i]! = val) ∧
  (∀ j : Nat, j < arr.size → arr[j]! ≥ val)

-- Precondition: array must be non-empty
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: result is max - min
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (maxVal : Int) (minVal : Int),
    isMaximum a maxVal ∧
    isMinimum a minVal ∧
    result = maxVal - minVal

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int):
  VerinaSpec.differenceMinMax_precond a ↔ LeetProofSpec.precondition a := by
  exact?

noncomputable section AristotleLemmas

/-
Folding the max function over a non-empty array results in the maximum element of the array.
-/
theorem LeetProofSpec.foldl_max_isMaximum (a : Array Int) (h : a.size > 0) :
  LeetProofSpec.isMaximum a (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!)) := by
    -- Convert the array `a` to a list `l` using `Array.toList`.
    set l : List ℤ := a.toList;
    -- Since `a` is non-empty, `l` is also non-empty, and we can apply the lemma for lists.
    have h_list_max : ∀ (l : List ℤ), l ≠ [] → isMaximum (l.toArray) (List.foldl (fun acc x => if x > acc then x else acc) (l.head!) l) := by
      intro l hl_nonempty
      have h_fold_max : ∀ (l : List ℤ), l ≠ [] → List.foldl (fun acc x => if x > acc then x else acc) (l.head!) l ∈ l ∧ ∀ x ∈ l, x ≤ List.foldl (fun acc x => if x > acc then x else acc) (l.head!) l := by
        intro l hl_nonempty
        induction' l using List.reverseRecOn with l ih;
        · contradiction;
        · by_cases h : l = [] <;> simp_all +decide [ List.foldl_append ];
          grind;
      specialize h_fold_max l hl_nonempty;
      refine' ⟨ _, _ ⟩;
      · obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 h_fold_max.1;
        use i.val;
        aesop;
      · aesop;
    convert h_list_max l ( by aesop ) using 1;
    rcases a with ⟨ ⟨ l ⟩ ⟩ <;> aesop

/-
Folding the min function over a non-empty array results in the minimum element of the array.
-/
theorem LeetProofSpec.foldl_min_isMinimum (a : Array Int) (h : a.size > 0) :
  LeetProofSpec.isMinimum a (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)) := by
    -- By definition of `Array.toList`, the minimum of `a.toList` is the same as the minimum of `a`.
    have h_min_toList : ∀ {l : List Int}, l ≠ [] → isMinimum (Array.mk l) (List.foldl (fun acc x => if x < acc then x else acc) (l.head!) l) := by
      intros l hl_nonempty
      induction' l using List.reverseRecOn with x l ih;
      · contradiction;
      · by_cases hx : x = [] <;> simp_all +decide [ LeetProofSpec.isMinimum ];
        constructor;
        · split_ifs <;> simp_all +decide [ List.getElem?_append ];
          · exact ⟨ x.length, Nat.lt_succ_self _, by aesop ⟩;
          · exact ⟨ ih.1.choose, Nat.lt_succ_of_lt ih.1.choose_spec.1, by simpa [ ih.1.choose_spec.1 ] using ih.1.choose_spec.2 ⟩;
        · grind;
    convert h_min_toList ( show a.toList ≠ [] from by aesop );
    rcases a with ⟨ ⟨ l ⟩ ⟩ <;> aesop

end AristotleLemmas

theorem postcondition_equiv (a : Array Int) (result : Int) (h_precond : VerinaSpec.differenceMinMax_precond a):
  VerinaSpec.differenceMinMax_postcond a result h_precond ↔ LeetProofSpec.postcondition a result := by
  -- By definition of `differenceMinMax_postcond`, we know that `result + a.foldl ... = a.foldl ...`.
  simp [VerinaSpec.differenceMinMax_postcond];
  -- By definition of `postcondition`, we know that `result = maxVal - minVal`.
  rw [LeetProofSpec.postcondition];
  have h_max_min : LeetProofSpec.isMaximum a (a.foldl (fun acc x => if acc < x then x else acc) a[0]!) ∧ LeetProofSpec.isMinimum a (a.foldl (fun acc x => if x < acc then x else acc) a[0]!) := by
    apply And.intro (LeetProofSpec.foldl_max_isMaximum a h_precond) (LeetProofSpec.foldl_min_isMinimum a h_precond);
  unfold LeetProofSpec.isMaximum LeetProofSpec.isMinimum at *;
  grind