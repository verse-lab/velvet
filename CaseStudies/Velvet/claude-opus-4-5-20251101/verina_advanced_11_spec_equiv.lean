/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fbd22854-d16a-4e8f-9372-71d8e745a531

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Int):
  VerinaSpec.findMajorityElement_precond lst ↔ LeetProofSpec.precondition lst

- theorem postcondition_equiv (lst : List Int) (result : Int) (h_precond : VerinaSpec.findMajorityElement_precond lst):
  VerinaSpec.findMajorityElement_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def findMajorityElement_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0

def findMajorityElement_postcond (lst : List Int) (result: Int) (h_precond : findMajorityElement_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  let count := fun x => (lst.filter (fun y => y = x)).length
  let n := lst.length
  let majority := count result > n / 2 ∧ lst.all (fun x => count x ≤ n / 2 ∨ x = result)
  (result = -1 → lst.all (count · ≤ n / 2) ∨ majority) ∧
  (result ≠ -1 → majority)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to check if an element is a majority element
def isMajorityElement (lst : List Int) (x : Int) : Prop :=
  lst.count x > lst.length / 2

-- Helper function to check if a majority element exists
def hasMajorityElement (lst : List Int) : Prop :=
  ∃ x, x ∈ lst ∧ isMajorityElement lst x

-- Precondition: no restrictions on input
def precondition (lst : List Int) : Prop :=
  True

-- Postcondition: result is either the majority element or -1
def postcondition (lst : List Int) (result : Int) : Prop :=
  (hasMajorityElement lst → (result ∈ lst ∧ isMajorityElement lst result)) ∧
  (¬hasMajorityElement lst → result = -1)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (lst : List Int):
  VerinaSpec.findMajorityElement_precond lst ↔ LeetProofSpec.precondition lst := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.findMajorityElement_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (lst : List Int) (result : Int) (h_precond : VerinaSpec.findMajorityElement_precond lst):
  VerinaSpec.findMajorityElement_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result := by
  -- Let's split the equivalence into two implications.
  apply Iff.intro;
  · rintro ⟨ h₁, h₂ ⟩;
    constructor;
    · unfold LeetProofSpec.hasMajorityElement LeetProofSpec.isMajorityElement;
      grind;
    · unfold LeetProofSpec.hasMajorityElement;
      contrapose! h₂;
      simp_all +decide [ List.filter_eq ];
      exact fun h => False.elim <| h₂.1 result ( by contrapose! h; simp_all +decide [ List.count_eq_zero_of_not_mem ] ) <| by simpa [ List.count ] using h;
  · -- Let's split the implication into two cases: when the result is -1 and when it is not.
    intro h_postcond
    cases' em (result = -1) with h h <;> simp_all +decide [ LeetProofSpec.postcondition ];
    · -- If the result is -1, then either there's no majority element or -1 is the majority element.
      simp [VerinaSpec.findMajorityElement_postcond, h_postcond];
      by_cases h : ∃ x ∈ lst, ( List.filter ( fun y => y = x ) lst ).length >(lst.length / 2) <;> simp_all +decide [ List.filter_eq ];
      -- Since there exists an x in the list such that the count of x is greater than half the length, by h_postcond, -1 must be in the list and its count must be greater than half the length.
      have h_neg1 : -1 ∈ lst ∧ (lst.count (-1)) > (lst.length / 2) := by
        exact h_postcond ⟨ _, h.choose_spec.1, h.choose_spec.2 ⟩;
      -- Since -1 is in the list and its count is greater than half the length, for any x in the list, if x is not -1, then the count of x must be less than or equal to half the length.
      have h_count_le_half : ∀ x ∈ lst, x ≠ -1 → (lst.count x) ≤ (lst.length / 2) := by
        intros x hx hx_ne_neg1
        have h_count_le_half : (lst.count x) + (lst.count (-1)) ≤ lst.length := by
          have h_count_le_half : ∀ {l : List ℤ}, (∀ x ∈ l, x = x) → List.count x l + List.count (-1) l ≤ l.length := by
            -- We can prove this by induction on the list.
            intro l hl
            induction' l with x l ih;
            · norm_num;
            · grind +ring;
          exact h_count_le_half fun _ _ => rfl;
        omega;
      exact Or.inr ⟨ h_neg1.2, fun x hx => if hx' : x = -1 then Or.inr hx' else Or.inl <| h_count_le_half x hx hx' ⟩;
    · unfold VerinaSpec.findMajorityElement_postcond;
      -- Since result is not -1, we need to show that the count of result is greater than half the length of the list and that all elements are either less than or equal to half the length or equal to result.
      have h_count : (List.filter (fun y => y = result) lst).length > lst.length / 2 := by
        simp_all +decide [ List.filter_eq ];
        exact h_postcond.1 h_postcond.2 |>.2;
      have h_all : ∀ x ∈ lst, (List.filter (fun y => y = x) lst).length ≤ lst.length / 2 ∨ x = result := by
        -- If x is not the result, then the count of x is less than or equal to half the length of the list because the result is the majority element.
        intros x hx
        by_cases hx_result : x = result;
        · exact Or.inr hx_result;
        · have h_count_x : (List.filter (fun y => y = x) lst).length + (List.filter (fun y => y = result) lst).length ≤ lst.length := by
            have h_count_x : ∀ {l : List ℤ}, (∀ x ∈ l, x = x) → (List.filter (fun y => y = x) l).length + (List.filter (fun y => y = result) l).length ≤ l.length := by
              -- We can prove this by induction on the list.
              intro l hl
              induction' l with y l ih;
              · norm_num;
              · grind;
            exact h_count_x fun _ _ => rfl;
          omega;
      aesop