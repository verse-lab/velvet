/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7a629f27-a830-49e7-868b-cfed44011920

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Nat) (target : Nat):
  VerinaSpec.removeElement_precond lst target ↔ LeetProofSpec.precondition lst target

- theorem postcondition_equiv (lst : List Nat) (target : Nat) (result : List Nat) (h_precond : VerinaSpec.removeElement_precond lst target):
  VerinaSpec.removeElement_postcond lst target result h_precond ↔ LeetProofSpec.postcondition lst target result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def removeElement_precond (lst : List Nat) (target : Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def removeElement_postcond (lst : List Nat) (target : Nat) (result: List Nat) (h_precond : removeElement_precond (lst) (target)): Prop :=
  -- !benchmark @start postcond
  -- 1. All elements equal to target are removed from the result.
  -- 2. All other elements are preserved in order.
  -- 3. No new elements are added.

  -- Helper predicate: result contains exactly the elements of lst that are not equal to target, in order
  let lst' := lst.filter (fun x => x ≠ target)
  result.zipIdx.all (fun (x, i) =>
    match lst'[i]? with
    | some y => x = y
    | none => false) ∧ result.length = lst'.length

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Postcondition clauses

-- The result contains no occurrences of the target
def ensures1 (lst : List Nat) (target : Nat) (result : List Nat) :=
  target ∉ result

-- Every element in the result was in the original list
def ensures2 (lst : List Nat) (target : Nat) (result : List Nat) :=
  ∀ x, x ∈ result → x ∈ lst

-- Every non-target element in the original list appears in the result
def ensures3 (lst : List Nat) (target : Nat) (result : List Nat) :=
  ∀ x, x ∈ lst → x ≠ target → x ∈ result

-- The result is a sublist of the original (preserves order)
def ensures4 (lst : List Nat) (target : Nat) (result : List Nat) :=
  result.Sublist lst

-- The count of each non-target element is preserved
def ensures5 (lst : List Nat) (target : Nat) (result : List Nat) :=
  ∀ x, x ≠ target → result.count x = lst.count x

def precondition (lst : List Nat) (target : Nat) :=
  True

-- no preconditions needed

def postcondition (lst : List Nat) (target : Nat) (result : List Nat) :=
  ensures1 lst target result ∧
  ensures2 lst target result ∧
  ensures3 lst target result ∧
  ensures4 lst target result ∧
  ensures5 lst target result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (lst : List Nat) (target : Nat):
  VerinaSpec.removeElement_precond lst target ↔ LeetProofSpec.precondition lst target := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.removeElement_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (lst : List Nat) (target : Nat) (result : List Nat) (h_precond : VerinaSpec.removeElement_precond lst target):
  VerinaSpec.removeElement_postcond lst target result h_precond ↔ LeetProofSpec.postcondition lst target result := by
  constructor <;> intro h;
  · -- By definition of `removeElement_postcond`, we know that `result` contains exactly the elements of `lst` that are not equal to `target`, in order.
    have h_elements : result = lst.filter (fun x => x ≠ target) := by
      -- By definition of `removeElement_postcond`, we know that `result` is equal to `lst.filter (fun x => x ≠ target)`.
      have h_eq : result = lst.filter (fun x => x ≠ target) := by
        have h_zip : ∀ i < result.length, result.get! i = (lst.filter (fun x => x ≠ target)).get! i := by
          intro i hi; have := h.1; simp_all +decide [ List.get?_eq_get ] ;
          -- Apply the hypothesis `this` with `a = result.get i` and `b = i`.
          specialize this (result.get! i) i; simp_all +decide [ List.get?_eq_get ] ;
          exact this ( by rw [ List.mem_iff_get ] ; exact ⟨ ⟨ i, by aesop ⟩, by aesop ⟩ )
        refine' List.ext_get _ _ <;> aesop;
      exact h_eq;
    -- By definition of `List.filter`, we know that `result` is a sublist of `lst` and contains no occurrences of `target`.
    simp [h_elements, LeetProofSpec.postcondition];
    unfold LeetProofSpec.ensures1 LeetProofSpec.ensures2 LeetProofSpec.ensures3 LeetProofSpec.ensures4 LeetProofSpec.ensures5; aesop;
  · -- By definition of `postcondition`, we know that `result` is a sublist of `lst` and `target ∉ result`.
    obtain ⟨h_sublist, h_target⟩ := h;
    -- By definition of `postcondition`, we know that `result` is a sublist of `lst` and `target ∉ result`. Therefore, `result` must be equal to `lst.filter (fun x => x ≠ target)`.
    have h_eq : result = lst.filter (fun x => x ≠ target) := by
      have h_perm : List.Perm result (lst.filter (fun x => x ≠ target)) := by
        -- Since the counts of all elements in result and the filtered list are equal, and result is a sublist of lst, we can conclude that result is a permutation of the filtered list.
        have h_perm : ∀ x, List.count x result = List.count x (lst.filter (fun x => x ≠ target)) := by
          -- By definition of `ensures5`, we know that for any x not equal to the target, the count of x in result is equal to the count of x in the original list.
          intros x
          by_cases hx : x = target;
          · rw [ List.count_eq_zero_of_not_mem, List.count_eq_zero_of_not_mem ] <;> aesop;
          · convert h_target.2.2.2 x hx using 1;
            rw [ List.count_filter ] ; aesop;
        exact?;
      have h_eq : List.Sublist result (lst.filter (fun x => x ≠ target)) := by
        have h_eq : List.Sublist result lst := by
          exact h_target.2.2.1;
        have h_eq : ∀ {l1 l2 : List ℕ}, List.Sublist l1 l2 → List.Sublist (List.filter (fun x => x ≠ target) l1) (List.filter (fun x => x ≠ target) l2) := by
          grind;
        convert h_eq ‹_› using 1;
        exact Eq.symm ( List.filter_eq_self.mpr fun x hx => by aesop );
      exact List.Sublist.eq_of_length_le h_eq ( by simpa using h_perm.length_eq.ge );
    grind