/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3756daae-9ab3-404a-a51f-e70dc35217b0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- def precondition_equiv (heights : List (Int)) :
  VerinaSpec.rain_precond heights ↔ LeetProofSpec.precondition heights

- def postcondition_equiv (heights : List (Int)) (result: Int) (h_precond : VerinaSpec.rain_precond (heights)) :
  VerinaSpec.rain_postcond heights result h_precond ↔ LeetProofSpec.postcondition heights result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def rain_precond (heights : List (Int)) : Prop :=
  -- !benchmark @start precond
  heights.all (fun h => h >= 0)

-- !benchmark @end precond

@[reducible]
def rain_postcond (heights : List (Int)) (result: Int) (h_precond : rain_precond (heights)) : Prop :=
  -- !benchmark @start postcond
  -- The result is the total amount of rainwater trapped by the given terrain
  -- If there are fewer than 3 elements, no water can be trapped
  result >= 0 ∧
  -- The result is non-negative
  if heights.length < 3 then result = 0 else
    -- Water trapped at each position is min(maxLeft, maxRight) - height
    result =
      let max_left_at := λ i =>
        let rec ml (j : Nat) (max_so_far : Int) : Int :=
          if j > i then max_so_far
          else ml (j+1) (max max_so_far (heights[j]!))
          termination_by i + 1 - j
        ml 0 0

      let max_right_at := λ i =>
        let rec mr (j : Nat) (max_so_far : Int) : Int :=
          if j >= heights.length then max_so_far
          else mr (j+1) (max max_so_far (heights[j]!))
          termination_by heights.length - j
        mr i 0

      let water_at := λ i =>
        max 0 (min (max_left_at i) (max_right_at i) - heights[i]!)

      let rec sum_water (i : Nat) (acc : Int) : Int :=
        if i >= heights.length then acc
        else sum_water (i+1) (acc + water_at i)
        termination_by heights.length - i

      sum_water 0 0

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: maximum of a list with default 0
def listMax (l : List Int) : Int :=
  l.foldl max 0

-- Helper: maximum height from index 0 to i (inclusive)
def maxLeft (heights : List Int) (i : Nat) : Int :=
  listMax (heights.take (i + 1))

-- Helper: maximum height from index i to end (inclusive)
def maxRight (heights : List Int) (i : Nat) : Int :=
  listMax (heights.drop i)

-- Helper: water trapped at a specific position
def waterAt (heights : List Int) (i : Nat) : Int :=
  let leftMax := maxLeft heights i
  let rightMax := maxRight heights i
  let waterLevel := min leftMax rightMax
  max (waterLevel - heights[i]!) 0

-- Precondition: all heights are non-negative
def allNonNegative (heights : List Int) : Prop :=
  ∀ i : Nat, i < heights.length → heights[i]! ≥ 0

def precondition (heights : List Int) :=
  allNonNegative heights

-- Postcondition: result equals the total trapped water
-- Water at each position i is: max(0, min(maxLeft, maxRight) - height[i])
-- Total water is the sum over all positions
def postcondition (heights : List Int) (result : Int) :=
  result = ((List.range heights.length).map (waterAt heights)).foldl (· + ·) 0

end LeetProofSpec

def precondition_equiv (heights : List (Int)) :
  VerinaSpec.rain_precond heights ↔ LeetProofSpec.precondition heights := by
  -- By definition of `VerinaSpec.rain_precond` and `LeetProofSpec.precondition`, they are equivalent because both state that all elements in the heights list are non-negative.
  simp [VerinaSpec.rain_precond, LeetProofSpec.precondition];
  -- The two conditions are equivalent because they both state that all elements in the list are non-negative.
  simp [LeetProofSpec.allNonNegative];
  -- The two conditions are equivalent because they both check that every element in the list is non-negative. The first condition uses the `all` function to check each element, while the second condition uses `getD` to access each element by index.
  apply Iff.intro;
  · aesop;
  · intro h x hx; obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hx; aesop;

noncomputable section AristotleLemmas

def VerinaHelpers_ml_aux (heights : List Int) (i : Nat) (j : Nat) (max_so_far : Int) : Int :=
  if j > i then max_so_far
  else VerinaHelpers_ml_aux heights i (j+1) (max max_so_far (heights[j]!))
termination_by i + 1 - j

def VerinaHelpers_mr_aux (heights : List Int) (j : Nat) (max_so_far : Int) : Int :=
  if j >= heights.length then max_so_far
  else VerinaHelpers_mr_aux heights (j+1) (max max_so_far (heights[j]!))
termination_by heights.length - j

def VerinaHelpers_sum_water_aux (heights : List Int) (water_at : Nat -> Int) (i : Nat) (acc : Int) : Int :=
  if i >= heights.length then acc
  else VerinaHelpers_sum_water_aux heights water_at (i+1) (acc + water_at i)
termination_by heights.length - i

theorem VerinaHelpers_ml_aux_eq_fold (heights : List Int) (i : Nat) (j : Nat) (acc : Int)
  (hi : i < heights.length) (hj : j <= i + 1) :
  VerinaHelpers_ml_aux heights i j acc = ((heights.take (i + 1)).drop j).foldl max acc := by
  induction' k : i + 1 - j with k ih generalizing j acc;
  · unfold VerinaHelpers_ml_aux;
    rw [ Nat.sub_eq_iff_eq_add ] at k <;> aesop;
  · convert ih ( j + 1 ) ( Max.max acc ( heights[j]! ) ) ( by omega ) ( by omega ) using 1;
    · rw [ VerinaHelpers_ml_aux ];
      grind;
    · rw [ List.drop_eq_getElem_cons ];
      grind;
      grind

theorem VerinaHelpers_mr_aux_eq_fold (heights : List Int) (j : Nat) (acc : Int) :
  VerinaHelpers_mr_aux heights j acc = (heights.drop j).foldl max acc := by
  induction' n : heights.length - j using Nat.strong_induction_on with n ih generalizing j acc;
  unfold VerinaHelpers_mr_aux;
  split_ifs <;> simp_all +decide [ List.drop ];
  · rw [ List.drop_eq_nil_of_le ] <;> aesop;
  · convert ih ( heights.length - ( j + 1 ) ) ( by omega ) ( j + 1 ) ( Max.max acc heights[j] ) _ using 1;
    · rw [ List.drop_eq_getElem_cons ];
      exact?;
    · rfl

theorem VerinaHelpers_sum_water_aux_eq_fold (heights : List Int) (water_at : Nat -> Int) (i : Nat) (acc : Int) :
  VerinaHelpers_sum_water_aux heights water_at i acc = List.foldl (fun x y => x + y) acc (List.map water_at (List.drop i (List.range heights.length))) := by
  induction' k : heights.length - i using Nat.strong_induction_on with k ih generalizing i acc;
  unfold VerinaHelpers_sum_water_aux;
  split_ifs <;> simp_all +decide [ List.drop ];
  · rw [ List.drop_eq_nil_of_le ] <;> aesop;
  · rw [ List.drop_eq_getElem_cons ];
    grind;
    simpa

theorem LeetProofSpec_result_nonneg (heights : List Int) (result : Int)
  (h : LeetProofSpec.postcondition heights result) : result >= 0 := by
  -- By definition of `waterAt`, each term in the sum is non-negative.
  have h_nonneg : ∀ i < heights.length, 0 ≤ LeetProofSpec.waterAt heights i := by
    exact fun i hi => le_max_of_le_right ( le_rfl );
  -- By definition of `List.foldl`, we can rewrite the sum as the sum of `waterAt` values.
  have h_sum : List.foldl (fun (x1 x2 : ℤ) => x1 + x2) 0 (List.map (LeetProofSpec.waterAt heights) (List.range heights.length)) = ∑ i ∈ Finset.range heights.length, LeetProofSpec.waterAt heights i := by
    induction' heights.length with n ih <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ];
  exact h.symm ▸ h_sum.symm ▸ Finset.sum_nonneg fun i hi => h_nonneg i ( Finset.mem_range.mp hi )

theorem LeetProofSpec_waterAt_eq_zero_of_small_with_precond (heights : List Int) (i : Nat)
  (h_len : heights.length < 3) (hi : i < heights.length)
  (h_precond : VerinaSpec.rain_precond heights) :
  LeetProofSpec.waterAt heights i = 0 := by
  rcases heights with ( _ | ⟨ a, _ | ⟨ b, _ | heights ⟩ ⟩ ) <;> rcases i with ( _ | i ) <;> simp_all +decide;
  · unfold LeetProofSpec.waterAt;
    simp +decide [ LeetProofSpec.maxLeft, LeetProofSpec.maxRight ];
    unfold LeetProofSpec.listMax; aesop;
  · unfold LeetProofSpec.waterAt;
    simp +decide [ LeetProofSpec.maxLeft, LeetProofSpec.maxRight ];
    unfold LeetProofSpec.listMax; aesop;
  · rcases i with ( _ | _ | i ) <;> norm_num [ LeetProofSpec.waterAt ] at *;
    · simp +decide [ LeetProofSpec.maxLeft, LeetProofSpec.maxRight ];
      simp +decide [ LeetProofSpec.listMax ];
      tauto;
    · linarith;
  · contradiction;
  · grind

theorem VerinaHelpers_ml_aux_unique (heights : List Int) (i : Nat) (f : Nat -> Int -> Int)
  (h_eq : ∀ j acc, f j acc = if j > i then acc else f (j+1) (max acc (heights[j]!))) :
  ∀ j acc, f j acc = VerinaHelpers_ml_aux heights i j acc := by
  intros j acc
  induction' k : i + 1 - j using Nat.strong_induction_on with k ih generalizing j acc;
  unfold VerinaHelpers_ml_aux; split_ifs <;> norm_num at * ;
  · rw [ h_eq, if_pos ‹_› ];
  · grind

theorem VerinaHelpers_mr_aux_unique (heights : List Int) (f : Nat -> Int -> Int)
  (h_eq : ∀ j acc, f j acc = if j >= heights.length then acc else f (j+1) (max acc (heights[j]!))) :
  ∀ j acc, f j acc = VerinaHelpers_mr_aux heights j acc := by
  -- We proceed by induction on `heights.length - j`.
  have h_ind : ∀ j, ∀ acc, j ≤ heights.length → f j acc = VerinaHelpers_mr_aux heights j acc := by
    intro j acc hj;
    induction' hn : heights.length - j using Nat.strong_induction_on with k ih generalizing j acc;
    by_cases h : j ≥ heights.length;
    · rw [ h_eq j acc, if_pos h ];
      unfold VerinaHelpers_mr_aux; simp +decide [ h ] ;
    · convert ih ( heights.length - ( j + 1 ) ) _ ( j + 1 ) ( Max.max acc heights[j]! ) _ _ using 1;
      · rw [ h_eq j acc, if_neg h ];
      · rw [ VerinaHelpers_mr_aux ];
        rw [ if_neg h ];
      · omega;
      · linarith;
      · rfl;
  intro j acc; specialize h_eq j acc; split_ifs at h_eq ;
  · unfold VerinaHelpers_mr_aux; aesop;
  · exact h_ind _ _ ( le_of_not_ge ‹_› )

theorem VerinaHelpers_sum_water_aux_unique (heights : List Int) (water_at : Nat -> Int) (f : Nat -> Int -> Int)
  (h_eq : ∀ i acc, f i acc = if i >= heights.length then acc else f (i+1) (acc + water_at i)) :
  ∀ i acc, f i acc = VerinaHelpers_sum_water_aux heights water_at i acc := by
  intro i acc;
  -- By induction on $k = \text{length} - i$, we can show that $f i acc = \text{VerinaHelpers_sum_water_aux} \, \text{heights} \, \text{water_at} \, i \, acc$.
  have h_ind : ∀ k, ∀ i acc, i + k = heights.length → f i acc = VerinaHelpers_sum_water_aux heights water_at i acc := by
    intro k
    induction' k with k ih k ih generalizing i acc;
    · intros i acc hi;
      unfold VerinaHelpers_sum_water_aux; simp +decide [ hi ] ;
      grind;
    · intro i acc hi;
      rw [ h_eq i acc, if_neg ( by linarith ) ];
      convert ih ( i + 1 ) ( acc + water_at i ) ( i + 1 ) ( acc + water_at i ) ( by linarith ) using 1;
      rw [ VerinaHelpers_sum_water_aux ];
      grind;
  by_cases hi : i < heights.length;
  · exact h_ind ( heights.length - i ) i acc ( by rw [ add_tsub_cancel_of_le hi.le ] );
  · rw [ h_eq i acc, if_pos ( le_of_not_gt hi ) ];
    unfold VerinaHelpers_sum_water_aux; simp +decide [ hi ] ;

theorem VerinaSpec_rain_postcond_eq_large (heights : List Int) (result : Int) (h_precond : VerinaSpec.rain_precond heights) (h_len : heights.length >= 3) :
  VerinaSpec.rain_postcond heights result h_precond ↔
  result = VerinaHelpers_sum_water_aux heights (fun i => max 0 (min (VerinaHelpers_ml_aux heights i 0 0) (VerinaHelpers_mr_aux heights i 0) - heights[i]!)) 0 0 := by
  constructor <;> intro h;
  · convert h.2 using 1;
    split_ifs <;> simp_all +decide [ VerinaSpec.rain_postcond ];
    · grind;
    · apply VerinaHelpers_sum_water_aux_unique;
      intro i acc; exact (by
      rw [ VerinaSpec.rain_postcond.sum_water ];
      congr! 3;
      congr! 3;
      · apply VerinaHelpers_ml_aux_unique;
        exact?;
      · apply VerinaHelpers_mr_aux_unique;
        exact?);
  · refine' ⟨ _, _ ⟩;
    · rw [ h, VerinaHelpers_sum_water_aux_eq_fold ];
      induction' heights.length with n ih <;> simp +decide [ List.range_succ ] at *;
      exact add_nonneg ih ( le_max_left _ _ );
    · rw [ if_neg ( by linarith ) ];
      convert h using 1;
      -- Apply the uniqueness lemmas to replace the internal functions with the helper functions.
      have h_unique : ∀ i, VerinaSpec.rain_postcond.ml heights i 0 0 = VerinaHelpers_ml_aux heights i 0 0 ∧ VerinaSpec.rain_postcond.mr heights i 0 = VerinaHelpers_mr_aux heights i 0 := by
        intros i
        constructor;
        · apply VerinaHelpers_ml_aux_unique;
          exact?;
        · apply VerinaHelpers_mr_aux_unique;
          exact?;
      simp +decide only [h_unique];
      convert VerinaHelpers_sum_water_aux_unique heights _ _ _ 0 0 using 1;
      exact?

end AristotleLemmas

def postcondition_equiv (heights : List (Int)) (result: Int) (h_precond : VerinaSpec.rain_precond (heights)) :
  VerinaSpec.rain_postcond heights result h_precond ↔ LeetProofSpec.postcondition heights result := by
  by_cases h_len : heights.length < 3;
  · unfold VerinaSpec.rain_postcond LeetProofSpec.postcondition;
    have h_water_zero : ∀ i < heights.length, LeetProofSpec.waterAt heights i = 0 := by
      exact?;
    rw [ show List.map ( LeetProofSpec.waterAt heights ) ( List.range heights.length ) = List.replicate heights.length 0 from ?_ ];
    · interval_cases _ : heights.length <;> simp_all +decide;
    · refine' List.ext_get _ _ <;> aesop;
  · constructor <;> intro h;
    · -- By definition of `VerinaSpec.rain_postcond`, we know that `result` is equal to the sum of `waterAt` for all positions.
      have h_sum_water : result = VerinaHelpers_sum_water_aux heights (fun i => max 0 (min (VerinaHelpers_ml_aux heights i 0 0) (VerinaHelpers_mr_aux heights i 0) - heights[i]!)) 0 0 := by
        convert VerinaSpec_rain_postcond_eq_large heights result h_precond ( by linarith ) |>.1 h;
      -- By definition of `VerinaHelpers_sum_water_aux`, we can rewrite the sum of `waterAt` using the foldl operation.
      have h_foldl : result = List.foldl (fun x y => x + y) 0 (List.map (fun i => max 0 (min (VerinaHelpers_ml_aux heights i 0 0) (VerinaHelpers_mr_aux heights i 0) - heights[i]!)) (List.range heights.length)) := by
        rw [h_sum_water];
        convert VerinaHelpers_sum_water_aux_eq_fold _ _ _ _ using 1;
      -- By definition of `VerinaHelpers_ml_aux` and `VerinaHelpers_mr_aux`, we can rewrite the sum of `waterAt` using the foldl operation.
      have h_foldl_eq : List.map (fun i => max 0 (min (VerinaHelpers_ml_aux heights i 0 0) (VerinaHelpers_mr_aux heights i 0) - heights[i]!)) (List.range heights.length) = List.map (fun i => LeetProofSpec.waterAt heights i) (List.range heights.length) := by
        refine' List.map_congr_left _;
        intro i hi;
        unfold LeetProofSpec.waterAt;
        simp +decide [ VerinaHelpers_ml_aux_eq_fold, VerinaHelpers_mr_aux_eq_fold, LeetProofSpec.listMax ];
        rw [ VerinaHelpers_ml_aux_eq_fold ] <;> norm_num;
        · exact max_comm _ _;
        · exact List.mem_range.mp hi;
      exact h_foldl.trans ( h_foldl_eq.symm ▸ rfl );
    · convert VerinaSpec_rain_postcond_eq_large heights result h_precond ( by linarith ) |>.2 _;
      convert h using 1;
      · ext; simp [LeetProofSpec.postcondition];
        rw [ ← h, eq_comm ];
      · convert h.symm using 1;
        convert VerinaHelpers_sum_water_aux_eq_fold heights _ _ _ using 2;
        unfold LeetProofSpec.waterAt;
        simp +decide [ LeetProofSpec.maxLeft, LeetProofSpec.maxRight, VerinaHelpers_ml_aux_eq_fold, VerinaHelpers_mr_aux_eq_fold ];
        intro a ha; rw [ max_comm ] ; rw [ VerinaHelpers_ml_aux_eq_fold ] ; aesop;
        · exact?;
        · linarith
