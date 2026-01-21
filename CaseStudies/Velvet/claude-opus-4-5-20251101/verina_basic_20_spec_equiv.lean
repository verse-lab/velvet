/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 374356e4-700b-4516-8731-dc0d6d1fa03a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int):
  VerinaSpec.uniqueProduct_precond arr ↔ LeetProofSpec.precondition arr

- theorem postcondition_equiv (arr : Array Int) (result : Int) (h_precond : VerinaSpec.uniqueProduct_precond arr):
  VerinaSpec.uniqueProduct_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result
-/

import Lean
import Mathlib.Tactic
import Std.Data.HashSet


namespace VerinaSpec

def uniqueProduct_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def uniqueProduct_postcond (arr : Array Int) (result: Int) (h_precond : uniqueProduct_precond (arr)) :=
  -- !benchmark @start postcond
  result - (arr.toList.eraseDups.foldl (· * ·) 1) = 0 ∧
  (arr.toList.eraseDups.foldl (· * ·) 1) - result = 0

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Property-based specification:
-- The result is the product of some list of distinct elements where:
-- 1. Every element in that list appears in the original array
-- 2. Every element in the original array appears in that list
-- 3. The list has no duplicates
-- Since multiplication is commutative and associative, the product is unique

def precondition (arr : Array Int) :=
  True

-- no preconditions needed

def postcondition (arr : Array Int) (result : Int) :=
  ∃ distinctList : List Int,
    (∀ x, x ∈ distinctList ↔ x ∈ arr.toList) ∧
    distinctList.Nodup ∧
    result = distinctList.prod

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int):
  VerinaSpec.uniqueProduct_precond arr ↔ LeetProofSpec.precondition arr := by
  exact Iff.rfl

theorem postcondition_equiv (arr : Array Int) (result : Int) (h_precond : VerinaSpec.uniqueProduct_precond arr):
  VerinaSpec.uniqueProduct_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result := by
  -- To prove the equivalence, we show that the distinctList in LeetProofSpec's postcondition is equivalent to the result of arr.toList.eraseDups.
  have h_distinctList : ∀ (arr : Array ℤ), ∃ distinctList : List ℤ, (∀ x, x ∈ distinctList ↔ x ∈ arr.toList) ∧ distinctList.Nodup ∧ distinctList = arr.toList.eraseDups := by
    -- By definition of `eraseDups`, the list `arr.toList.eraseDups` contains exactly the distinct elements of `arr.toList`.
    have h_distinctList : ∀ (arr : Array ℤ), (∀ x, x ∈ arr.toList.eraseDups ↔ x ∈ arr.toList) ∧ (arr.toList.eraseDups).Nodup := by
      -- To prove the equivalence, we show that the distinctList in LeetProofSpec's postcondition is equivalent to the result of arr.toList.eraseDups. We can use the fact that `List.eraseDups` removes duplicates and preserves the order.
      have h_eraseDups : ∀ (l : List ℤ), (∀ x, x ∈ l.eraseDups ↔ x ∈ l) ∧ l.eraseDups.Nodup := by
        intro l;
        induction' l using List.reverseRecOn with l ih;
        · aesop;
        · simp_all +decide [ List.eraseDups_append ];
          simp_all +decide [ List.removeAll ];
          by_cases h : ih ∈ l <;> simp_all +decide [ List.eraseDups_cons ];
          rw [ List.nodup_append ] ; aesop;
      exact fun arr => h_eraseDups arr.toList;
    exact fun arr => ⟨ _, h_distinctList arr |>.1, h_distinctList arr |>.2, rfl ⟩;
  -- By definition of `uniqueProduct_postcond`, we know that `result` is the product of the distinct elements in `arr`.
  have h_uniqueProduct : result = (arr.toList.eraseDups).prod ↔ ∃ distinctList : List ℤ, (∀ x, x ∈ distinctList ↔ x ∈ arr.toList) ∧ distinctList.Nodup ∧ result = distinctList.prod := by
    simp +zetaDelta at *;
    -- By definition of `uniqueProduct_postcond`, we know that `result` is the product of the distinct elements in `arr.toList`. Therefore, the equivalence holds.
    apply Iff.intro;
    · exact fun h => ⟨ _, h_distinctList arr |>.1, h_distinctList arr |>.2, h ⟩;
    · -- Since distinctList is a permutation of arr.toList.eraseDups, their products are equal.
      intros h
      obtain ⟨distinctList, h_distinctList⟩ := h
      have h_perm : List.Perm distinctList (arr.toList.eraseDups) := by
        grind;
      rw [ h_distinctList.2.2, h_perm.prod_eq ];
  -- By definition of `uniqueProduct_postcond`, we know that `result` is the product of the distinct elements in `arr`, which is equivalent to the existence of a distinct list with the same properties.
  simp [VerinaSpec.uniqueProduct_postcond, LeetProofSpec.postcondition, h_uniqueProduct];
  -- By definition of `List.prod`, we know that `List.foldl (fun x1 x2 => x1 * x2) 1 l = l.prod` for any list `l`.
  have h_foldl_prod : ∀ (l : List ℤ), List.foldl (fun x1 x2 => x1 * x2) 1 l = l.prod := by
    exact?;
  grind