import Lean
import Mathlib.Tactic

def ensures1 (dataset : List Nat) (n : Nat) (result : List Nat) :=
  result = (dataset.mergeSort (· ≤ ·)).take n  -- result is exactly the first n elements of sorted dataset

def precondition (dataset: List Nat) (n: Nat) :=
  True

def postcondition (dataset: List Nat) (n: Nat) (result: List Nat) :=
  ensures1 dataset n result

-- Test Cases
def test0_dataset : List Nat := [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100]

def test0_n : Nat := 2

def test0_Expected : List Nat := [10, 20]

def test1_dataset : List Nat := [7, 10, 4, 3, 20, 15]

def test1_n : Nat := 3

def test1_Expected : List Nat := [3, 4, 7]

def test2_dataset : List Nat := [5, 2, 8]

def test2_n : Nat := 5

def test2_Expected : List Nat := [2, 5, 8]

def test3_dataset : List Nat := [1, 2, 3]

def test3_n : Nat := 0

def test3_Expected : List Nat := []

def test4_dataset : List Nat := []

def test4_n : Nat := 3

def test4_Expected : List Nat := []

def test5_dataset : List Nat := [4, 1, 4, 2, 4, 1]

def test5_n : Nat := 4

def test5_Expected : List Nat := [1, 1, 2, 4]

-------------------------------
-- Verifications
-------------------------------

-- test0
lemma test0_precondition :
  precondition test0_dataset test0_n := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test0_postcondition :
  postcondition test0_dataset test0_n test0_Expected := by
  -- Let's sort the dataset and take the first n elements.
  have h_sorted : (test0_dataset.mergeSort (· ≤ ·)) = [10, 20, 20, 40, 50, 50, 60, 70, 80, 90, 100] := by
    native_decide;
  -- Apply the hypothesis `h_sorted` to conclude the proof.
  rw [postcondition, ensures1, h_sorted];
  -- By definition of `test0_Expected`, we know that it is equal to the first two elements of the sorted list.
  simp [test0_Expected, test0_n]

-- test1
lemma test1_precondition :
  precondition test1_dataset test1_n := by
  exact?

lemma test1_postcondition :
  postcondition test1_dataset test1_n test1_Expected := by
  -- By definition of `postcondition`, we need to show that the result is the first `n` elements of the sorted dataset.
  simp [postcondition, ensures1];
  native_decide

-- test2
lemma test2_precondition :
  precondition test2_dataset test2_n := by
  trivial

lemma test2_postcondition :
  postcondition test2_dataset test2_n test2_Expected := by
  -- By definition of `postcondition`, we need to show that the result is the first `n` elements of the sorted dataset.
  simp [postcondition, test2_dataset, test2_n, test2_Expected];
  -- The sorted list of [5, 2, 8] is [2, 5, 8], and taking the first 5 elements of this sorted list gives [2, 5, 8].
  simp [ensures1, List.mergeSort]

-- test3
lemma test3_precondition :
  precondition test3_dataset test3_n := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test3_postcondition :
  postcondition test3_dataset test3_n test3_Expected := by
  -- By definition of `postcondition`, we know that `postcondition test3_dataset test3_n test3_Expected` holds.
  unfold postcondition;
  -- Since the dataset is [1, 2, 3] and n is 0, the sorted dataset is [1, 2, 3], and taking the first 0 elements gives the empty list.
  simp [ensures1, test3_dataset, test3_n, test3_Expected]

-- test4
lemma test4_precondition :
  precondition test4_dataset test4_n := by
  exact?

lemma test4_postcondition :
  postcondition test4_dataset test4_n test4_Expected := by
  -- Since the dataset is empty, the sorted dataset is also empty, and taking 3 elements from it gives the empty list.
  simp [postcondition, test4_dataset, test4_n, test4_Expected];
  -- Since the dataset is empty, the sorted dataset is also empty, and taking 3 elements from it gives the empty list. Therefore, the postcondition holds.
  simp [ensures1]

-- test5
lemma test5_precondition :
  precondition test5_dataset test5_n := by
  exact?

lemma test5_postcondition :
  postcondition test5_dataset test5_n test5_Expected := by
  -- By definition of `postcondition`, we need to show that the result of taking the first 4 elements of the sorted dataset [4, 1, 4, 2, 4, 1] is [1, 1, 2, 4].
  simp [postcondition, ensures1, test5_dataset, test5_n, test5_Expected];
  -- Apply the merge sort algorithm to the list [4, 1, 4, 2, 4, 1].
  simp [List.mergeSort]

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (dataset: List Nat) (n: Nat):
  precondition dataset n →
  (∀ ret1 ret2,
    postcondition dataset n ret1 →
    postcondition dataset n ret2 →
    ret1 = ret2) := by
  -- By definition of postcondition, if ret1 and ret2 are both postconditions, then they must be equal to the same sorted list.
  intros h_precondition ret1 ret2 h_ret1 h_ret2
  rw [h_ret1, h_ret2]
