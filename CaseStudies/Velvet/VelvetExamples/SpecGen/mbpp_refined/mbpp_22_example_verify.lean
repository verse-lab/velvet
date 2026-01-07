import Lean
import Mathlib.Tactic

def ensures1 (arr : List Int) (result : Option Int) :=
  match result with
  | none => ∀ i j, i < j → j < arr.length → arr[i]! ≠ arr[j]!
  | some x =>
      ∃ i j, (i < j ∧ j < arr.length ∧ arr[i]! = x ∧ arr[j]! = x) ∧
              (∀ i' j', i' < j' → j' < arr.length → arr[i']! = arr[j']! → j ≤ j')

def precondition (arr: List Int) :=
  True

def postcondition (arr: List Int) (result: Option Int) :=
  ensures1 arr result

-- Test Cases
def test0_arr : List Int := [1, 2, 3, 4, 4, 5]

def test0_Expected : Option Int := some 4

def test1_arr : List Int := [1, 2, 3, 2, 4, 1]

def test1_Expected : Option Int := some 2

def test2_arr : List Int := [1, 2, 3, 4, 5]

def test2_Expected : Option Int := none

def test3_arr : List Int := [1, 1, 2, 3]

def test3_Expected : Option Int := some 1

def test4_arr : List Int := []

def test4_Expected : Option Int := none

def test6_arr : List Int := [7, 7, 7, 7]

def test6_Expected : Option Int := some 7

-------------------------------
-- Verifications
-------------------------------

-- test0
lemma test0_precondition :
  precondition test0_arr := by
  trivial

lemma test0_postcondition :
  postcondition test0_arr test0_Expected := by
  -- For the test0_arr, the first duplicate is at indices 3 and 4, so the postcondition holds.
  simp [postcondition, test0_arr, test0_Expected];
  -- We can see that the element 4 appears at indices 3 and 4.
  use 3, 4
  simp +decide [ensures1];
  -- By examining all possible pairs (i', j') where i' < j' and j' < 6, we can verify that the only pair with equal elements is (3,4), and in that case, j' = 4.
  intros i' j' hij' hj' h_eq
  interval_cases j' <;> interval_cases i' <;> simp +decide at h_eq ⊢

-- test1
lemma test1_precondition :
  precondition test1_arr := by
  trivial

lemma test1_postcondition :
  postcondition test1_arr test1_Expected := by
  -- We need to show that 2 is the first duplicate element in the list [1, 2, 3, 2, 4, 1].
  -- We can verify this by checking each element and confirming that 2 appears twice with the smallest second occurrence index.
  simp [ensures1, test1_arr, test1_Expected];
  -- Let's choose the indices $i = 1$ and $j = 3$.
  use 1, 3;
  grind

-- test2
lemma test2_precondition :
  precondition test2_arr := by
  exact?

lemma test2_postcondition :
  postcondition test2_arr test2_Expected := by
  -- For the test case test2_arr, which is [1, 2, 3, 4, 5], we need to show that the result is none because there are no duplicates. We can do this by checking all pairs of indices.
  simp [postcondition, test2_arr, test2_Expected];
  -- We'll use that all elements in the list are distinct to show that the postcondition holds.
  intro i j hij hlt hneq
  aesop;
  -- Since $j < 5$, we can check all possible values of $j$ and show that there are no duplicates.
  interval_cases j <;> interval_cases i <;> simp +decide at hneq ⊢

-- test3
lemma test3_precondition :
  precondition test3_arr := by
  -- The precondition for test3_arr is trivially true.
  simp [precondition]

lemma test3_postcondition :
  postcondition test3_arr test3_Expected := by
  -- For the array [1, 1, 2, 3], the first duplicate is at indices 0 and 1. The value is 1.
  simp [postcondition, test3_arr, test3_Expected];
  -- We need to show that there exists a pair (i, j) with i < j, j < 4, and arr[i]! = arr[j]! = 1, and that this pair has the smallest j.
  use 0, 1
  simp;
  -- Since $i' < j'$ and $j' < 4$, the smallest possible value for $j'$ is 1.
  intros i' j' hij hj' h_eq
  linarith

-- test4
lemma test4_precondition :
  precondition test4_arr := by
  -- The precondition for the empty list is trivially true.
  simp [precondition]

lemma test4_postcondition :
  postcondition test4_arr test4_Expected := by
  -- The postcondition for the empty list is trivially satisfied since there are no duplicates.
  simp [postcondition, ensures1];
  -- Since the list is empty, there are no elements to compare, so the condition is vacuously true.
  simp [test4_arr, test4_Expected]

-- test6
lemma test6_precondition :
  precondition test6_arr := by
  exact?

lemma test6_postcondition :
  postcondition test6_arr test6_Expected := by
  -- We need to show that 7 is indeed the first duplicate element in the list [7, 7, 7, 7].
  simp +decide [test6_arr, test6_Expected] at *;
  -- Let's choose i = 0 and j = 1.
  use 0, 1;
  grind

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (arr: List Int):
  precondition arr →
  (∀ ret1 ret2,
    postcondition arr ret1 →
    postcondition arr ret2 →
    ret1 = ret2) := by
  intros h1 ret1 ret2 h2 h3;
  unfold postcondition at *;
  unfold ensures1 at *;
  cases ret1 <;> cases ret2 <;> simp_all +decide;
  · grind;
  · grind;
  · grind
