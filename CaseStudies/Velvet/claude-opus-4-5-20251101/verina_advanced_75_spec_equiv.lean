/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 785c278c-45fe-4a92-b464-46a91d6f2b04

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (sequence : List Int):
  VerinaSpec.task_code_precond sequence ↔ LeetProofSpec.precondition sequence

- theorem postcondition_equiv (sequence : List Int) (result : Int) (h_precond : VerinaSpec.task_code_precond sequence):
  VerinaSpec.task_code_postcond sequence result h_precond ↔ LeetProofSpec.postcondition sequence result
-/

import Lean
import Mathlib.Tactic


namespace VerinaSpec

def task_code_precond (sequence : List Int) : Prop :=
  -- !benchmark @start precond
  sequence.length > 0

-- At least one element must be selected
  -- !benchmark @end precond

def task_code_postcond (sequence : List Int) (result: Int) (h_precond : task_code_precond (sequence)) : Prop :=
  -- !benchmark @start postcond
  let subArrays :=
    List.range (sequence.length + 1) |>.flatMap (fun start =>
      List.range (sequence.length - start + 1) |>.map (fun len =>
        sequence.drop start |>.take len))
  let subArraySums := subArrays.filter (· ≠ []) |>.map (·.sum)
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper function to compute the sum of a contiguous subarray from index start to index stop (exclusive)
def subarraySum (seq : List Int) (start : Nat) (stop : Nat) : Int :=
  (seq.drop start).take (stop - start) |>.foldl (· + ·) 0

-- Predicate: checks if (start, stop) defines a valid non-empty contiguous subarray
def isValidSubarray (seq : List Int) (start : Nat) (stop : Nat) : Prop :=
  start < stop ∧ stop ≤ seq.length

-- Predicate: the result is achievable by some contiguous non-empty subarray
def isAchievable (seq : List Int) (result : Int) : Prop :=
  ∃ start stop, isValidSubarray seq start stop ∧ subarraySum seq start stop = result

-- Predicate: the result is maximal among all contiguous non-empty subarrays
def isMaximal (seq : List Int) (result : Int) : Prop :=
  ∀ start stop, isValidSubarray seq start stop → subarraySum seq start stop ≤ result

-- Precondition: the sequence must be non-empty
def precondition (sequence : List Int) : Prop :=
  sequence.length > 0

-- Postcondition: the result is achievable and maximal
def postcondition (sequence : List Int) (result : Int) : Prop :=
  isAchievable sequence result ∧ isMaximal sequence result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (sequence : List Int):
  VerinaSpec.task_code_precond sequence ↔ LeetProofSpec.precondition sequence := by
  aesop

theorem postcondition_equiv (sequence : List Int) (result : Int) (h_precond : VerinaSpec.task_code_precond sequence):
  VerinaSpec.task_code_postcond sequence result h_precond ↔ LeetProofSpec.postcondition sequence result := by
  unfold VerinaSpec.task_code_postcond LeetProofSpec.postcondition;
  constructor <;> intro h;
  · constructor;
    · -- By definition of `subArraySums`, if `result` is in `subArraySums`, then there exists a subarray of `sequence` whose sum is `result`.
      obtain ⟨subarray, h_subarray⟩ : ∃ subarray ∈ List.filter (fun x => x ≠ []) (List.flatMap (fun start => List.map (fun len => List.take len (List.drop start sequence)) (List.range (sequence.length - start + 1))) (List.range (sequence.length + 1))), subarray.sum = result := by
        aesop;
      -- By definition of `subarray`, there exists a start and stop such that the subarray is the take of the drop of the sequence from start to stop.
      obtain ⟨start, stop, h_subarray_def⟩ : ∃ start stop, start < stop ∧ stop ≤ sequence.length ∧ subarray = List.take (stop - start) (List.drop start sequence) := by
        -- By definition of `subarray`, there exists a start and stop such that the subarray is the take of the drop of the sequence from start to stop. Use this fact.
        obtain ⟨start, len, h_subarray_def⟩ : ∃ start len, start < sequence.length + 1 ∧ len < sequence.length - start + 1 ∧ subarray = List.take len (List.drop start sequence) := by
          rw [ List.mem_filter ] at h_subarray ; aesop;
        by_cases h_len_zero : len = 0;
        · simp_all +decide [ List.mem_filter ];
        · exact ⟨ start, start + len, by linarith [ Nat.pos_of_ne_zero h_len_zero ], by omega, by simpa using h_subarray_def.2.2 ⟩;
      -- By definition of `subarraySum`, we can rewrite the sum of the subarray as the sum of the elements from start to stop-1.
      have h_sum_eq : subarray.sum = List.foldl (· + ·) 0 (List.take (stop - start) (List.drop start sequence)) := by
        rw [ h_subarray_def.2.2, List.sum_eq_foldl ];
      exact ⟨ start, stop, ⟨ h_subarray_def.1, h_subarray_def.2.1 ⟩, h_sum_eq.symm.trans h_subarray.2 ⟩;
    · intro start stop h_subarray
      obtain ⟨h_start, h_stop⟩ := h_subarray;
      -- By definition of `subarraySum`, we have `subarraySum sequence start stop = (List.take (stop - start) (List.drop start sequence)).sum`.
      have h_subarray_sum : LeetProofSpec.subarraySum sequence start stop = (List.take (stop - start) (List.drop start sequence)).sum := by
        unfold LeetProofSpec.subarraySum;
        exact?;
      simp_all +decide [ List.flatMap ];
      exact h.2 start ( by linarith ) ( stop - start ) ( by omega ) |> Or.rec ( fun h => by omega ) fun h => h;
  · -- By definition of `isAchievable`, there exists a subarray whose sum is `result`.
    obtain ⟨start, stop, h_subarray, h_sum⟩ := h.left;
    -- By definition of `isMaximal`, for any subarray, its sum is less than or equal to `result`.
    have h_max : ∀ start stop, LeetProofSpec.isValidSubarray sequence start stop → List.sum ((List.drop start sequence).take (stop - start)) ≤ result := by
      intros start stop h_subarray
      have h_sum : List.sum ((List.drop start sequence).take (stop - start)) = List.foldl (· + ·) 0 ((List.drop start sequence).take (stop - start)) := by
        rw [ List.sum_eq_foldl ];
      exact h_sum.symm ▸ h.2 start stop h_subarray;
    constructor;
    · -- Since `result` is the sum of a subarray from `start` to `stop`, it must be included in the list of subarray sums.
      have h_subarray_in_list : List.take (stop - start) (List.drop start sequence) ∈ List.flatMap (fun start => List.map (fun len => List.take len (List.drop start sequence)) (List.range (sequence.length - start + 1))) (List.range (sequence.length + 1)) := by
        simp +zetaDelta at *;
        exact ⟨ start, Nat.lt_succ_of_le ( by linarith [ h_subarray.1, h_subarray.2 ] ), stop - start, Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ h_subarray.1, h_subarray.2, Nat.sub_add_cancel ( show start ≤ sequence.length from by linarith [ h_subarray.1, h_subarray.2 ] ) ] ), rfl ⟩;
      simp_all +decide [ List.mem_filter, List.mem_map ];
      use List.take (stop - start) (List.drop start sequence);
      simp_all +decide [ LeetProofSpec.subarraySum ];
      exact ⟨ ⟨ Nat.sub_ne_zero_of_lt h_subarray.1, by linarith [ h_subarray.1, h_subarray.2 ] ⟩, by rw [ ← h_sum, List.sum_eq_foldl ] ⟩;
    · simp_all +decide [ List.all_eq_true ];
      exact fun x hx y hy => Classical.or_iff_not_imp_left.2 fun h => h_max x ( x + y ) ⟨ by omega, by omega ⟩ |> fun h' => by simpa [ add_tsub_cancel_of_le ( show x ≤ x + y from Nat.le_add_right _ _ ) ] using h';