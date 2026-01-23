/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f9c4cbcc-fe21-4adf-8cdf-0eab8bdbcd92

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int):
  VerinaSpec.FindEvenNumbers_precond arr ↔ LeetProofSpec.precondition arr

- theorem postcondition_equiv (arr : Array Int) (result : Array Int) (h_precond : VerinaSpec.FindEvenNumbers_precond arr):
  VerinaSpec.FindEvenNumbers_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def isEven (n : Int) : Bool :=
  n % 2 = 0

def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

def FindEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : FindEvenNumbers_precond (arr)) :=
  -- !benchmark @start postcond
  result.all (fun x => isEven x) ∧
  result.toList.Sublist arr.toList ∧
  result.size = arr.toList.countP isEven

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function: check if an integer is even
def isEven (n : Int) : Prop := n % 2 = 0

-- Postcondition clause 1: result is a sublist of input (preserves order)
def ensures1 (arr : Array Int) (result : Array Int) : Prop :=
  result.toList.Sublist arr.toList

-- Postcondition clause 2: all elements in result are even
def ensures2 (result : Array Int) : Prop :=
  ∀ i : Nat, i < result.size → result[i]! % 2 = 0

-- Postcondition clause 3: count preservation for even elements
def ensures3 (arr : Array Int) (result : Array Int) : Prop :=
  ∀ x : Int, x % 2 = 0 → result.toList.count x = arr.toList.count x

-- Postcondition clause 4: odd elements have count 0 in result
def ensures4 (result : Array Int) : Prop :=
  ∀ x : Int, x % 2 ≠ 0 → result.toList.count x = 0

def precondition (arr : Array Int) : Prop :=
  True

-- no preconditions

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  ensures1 arr result ∧
  ensures2 result ∧
  ensures3 arr result ∧
  ensures4 result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (arr : Array Int):
  VerinaSpec.FindEvenNumbers_precond arr ↔ LeetProofSpec.precondition arr := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.FindEvenNumbers_precond, LeetProofSpec.precondition]

theorem postcondition_equiv (arr : Array Int) (result : Array Int) (h_precond : VerinaSpec.FindEvenNumbers_precond arr):
  VerinaSpec.FindEvenNumbers_postcond arr result h_precond ↔ LeetProofSpec.postcondition arr result := by
  -- By definition of `postcondition`, we know that if the result is a sublist of the input array and all elements are even, then the counts of even numbers are preserved and the counts of odd numbers are zero.
  simp [LeetProofSpec.postcondition, LeetProofSpec.ensures1, LeetProofSpec.ensures2, LeetProofSpec.ensures3, LeetProofSpec.ensures4];
  constructor;
  · intro h;
    unfold VerinaSpec.FindEvenNumbers_postcond at h;
    -- Since `result` is a sublist of `arr` and all elements in `result` are even, the counts of even numbers in `result` and `arr` are preserved, and the counts of odd numbers in `result` are zero.
    have h_even_count : ∀ x : ℤ, 2 ∣ x → result.toList.count x = arr.toList.count x := by
      intros x hx_even
      have h_count_eq : List.count x result.toList = List.count x (List.filter (fun x => VerinaSpec.isEven x) arr.toList) := by
        have h_count_eq : List.count x result.toList = List.count x (List.filter (fun x => VerinaSpec.isEven x) result.toList) := by
          rw [ List.filter_eq_self.mpr ];
          simp_all +decide [ Array.all_eq ];
          intro a ha; obtain ⟨ i, hi ⟩ := Array.mem_iff_getElem.mp ha; aesop;
        have h_count_eq : List.length (List.filter (fun x => VerinaSpec.isEven x) result.toList) = List.length (List.filter (fun x => VerinaSpec.isEven x) arr.toList) := by
          convert h.2.2 using 1;
          · rw [ List.filter_eq_self.mpr ] ; aesop;
            intro a ha; obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp ha; aesop;
          · grind;
        grind;
      rw [ h_count_eq, List.count_filter ];
      unfold VerinaSpec.isEven; obtain ⟨ k, rfl ⟩ := hx_even; norm_num;
    simp_all +decide [ VerinaSpec.isEven, List.count_eq_zero ];
    -- Since `result` is a sublist of `arr` and all elements in `result` are even, any element in `result` must be even. Therefore, if `x` is odd, it cannot be in `result`, so its count is zero.
    intros x hx_odd
    have h_not_in_result : x ∉ result.toList := by
      intro hx_in_result
      have h_even : 2 ∣ x := by
        obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hx_in_result; aesop;
      simp_all +decide only [Int.dvd_iff_emod_eq_zero];
    rw [ Array.count ] ; aesop;
  · intro h;
    refine' ⟨ _, h.1, _ ⟩;
    · simp_all +decide [ VerinaSpec.isEven ];
    · -- By definition of `countP`, we know that `List.countP (fun x => x % 2 = 0) arr.toList` is equal to the number of even elements in `arr`.
      have h_countP : List.countP (fun x => x % 2 = 0) arr.toList = ∑ x ∈ arr.toList.toFinset, (arr.toList.count x) * if x % 2 = 0 then 1 else 0 := by
        have h_countP : ∀ {l : List ℤ}, List.countP (fun x => x % 2 = 0) l = ∑ x ∈ l.toFinset, (l.count x) * if x % 2 = 0 then 1 else 0 := by
          -- The count of even numbers in a list is equal to the sum of the counts of each even element in the list.
          intros l
          induction' l with x l ih;
          · rfl;
          · by_cases hx : x ∈ l <;> simp_all +decide [ List.count_cons ];
            · simp_all +decide [ List.countP_cons, Finset.sum_add_distrib ];
              simp +decide [ Finset.sum_add_distrib, Finset.sum_ite, hx ];
            · simp_all +decide [ List.countP_cons, Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc ];
              split_ifs <;> simp_all +decide [ List.count_eq_zero_of_not_mem ];
              · exact Finset.sum_congr rfl fun y hy => by aesop;
              · exact Finset.sum_congr rfl fun y hy => by aesop;
        apply h_countP;
      -- By definition of `countP`, we know that `List.countP (fun x => x % 2 = 0) result.toList` is equal to the number of even elements in `result`.
      have h_countP_result : List.countP (fun x => x % 2 = 0) result.toList = ∑ x ∈ arr.toList.toFinset, (result.toList.count x) * if x % 2 = 0 then 1 else 0 := by
        have h_countP_result : ∀ {l : List ℤ}, (∀ x ∈ l, x ∈ arr.toList.toFinset) → List.countP (fun x => x % 2 = 0) l = ∑ x ∈ arr.toList.toFinset, (l.count x) * if x % 2 = 0 then 1 else 0 := by
          -- We can prove this by induction on the list `l`.
          intro l hl
          induction' l with x l ih;
          · simp +decide [ List.countP_nil ];
          · by_cases hx : 2 ∣ x <;> simp_all +decide [ List.count_cons ];
            · simp +decide [ Finset.sum_add_distrib, Finset.sum_ite, hx ];
              exact hl.1;
            · simp_all +decide [ Finset.sum_add_distrib, Finset.sum_ite, Int.emod_eq_zero_of_dvd ];
        exact h_countP_result fun x hx => by have := h.1.subset hx; aesop;
      convert h_countP_result using 1;
      · rw [ List.countP_eq_length_filter ];
        rw [ List.filter_eq_self.mpr ] ; aesop;
        -- Since every element in the result list is even, for any a in the result list, a % 2 = 0.
        intros a ha
        have h_even : 2 ∣ a := by
          obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 ha; aesop;
        exact decide_eq_true ( Int.emod_eq_zero_of_dvd h_even );
      · convert h_countP using 2;
        aesop