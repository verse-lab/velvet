import Lean
import Mathlib.Tactic

-- Helper Functions

def allDifferent (lst: List Int) : Prop :=
  ∀ i j, i < lst.length → j < lst.length → i ≠ j → lst[i]! ≠ lst[j]!

def ensures1 (lst : List Int) (result : Bool) :=
  result = true ↔ allDifferent lst

def precondition (lst: List Int) :=
  True

def postcondition (lst: List Int) (result: Bool) :=
  ensures1 lst result

-- Test Cases
def test1_lst : List Int := [1, 5, 7, 9]

def test1_Expected : Bool := true

def test2_lst : List Int := [1, 2, 3, 2, 4]

def test2_Expected : Bool := false

def test3_lst : List Int := []

def test3_Expected : Bool := true

def test4_lst : List Int := [42]

def test4_Expected : Bool := true

def test6_lst : List Int := [5, 5]

def test6_Expected : Bool := false

def test13_lst : List Int := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
   21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,
   41,42,43,44,45,46,47,48,49,50]

def test13_Expected : Bool := true

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_lst := by
  exact?

lemma test1_postcondition :
  postcondition test1_lst test1_Expected := by
  -- Let's unfold the definition of `postcondition` to see what we need to prove.
  unfold postcondition;
  -- We'll use the fact that `test1_lst` is `[1, 5, 7, 9]` to check if all elements are different.
  simp [ensures1, test1_lst, test1_Expected];
  -- We can verify that all elements in the list [1, 5, 7, 9] are distinct by checking each pair.
  intro i j hi hj hij
  aesop;
  -- Let's check each possible pair (i, j) where i < j.
  interval_cases i <;> interval_cases j <;> simp at hij a

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_lst := by
  exact?

lemma test2_postcondition :
  postcondition test2_lst test2_Expected := by
  -- For ensures1, since the result is false, the implication is vacuously true.
  simp [postcondition, ensures1];
  -- Since the result is false, we need to show that not all elements are different.
  simp [test2_Expected, allDifferent];
  -- Let's choose any two different indices in the list [1, 2, 3, 2, 4].
  use 1, by decide, 3, by decide
  aesop

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_lst := by
  exact?

lemma test3_postcondition :
  postcondition test3_lst test3_Expected := by
  -- Show that the postcondition holds for the empty list.
  simp [postcondition, test3_Expected];
  -- Show that the postcondition holds for test3.
  simp [ensures1];
  -- Since the list [42] has only one element, there are no two different indices to compare, so the condition is trivially satisfied.
  simp [allDifferent, test3_lst]

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_lst := by
  exact?

lemma test4_postcondition :
  postcondition test4_lst test4_Expected := by
  -- By definition of `postcondition`, we need to show that `test4_Expected = true` if and only if `allDifferent test4_lst`.
  simp [postcondition];
  -- By definition of `test4_lst` and `test4_Expected`, we have that `allDifferent test4_lst` holds.
  simp [test4_Expected, ensures1];
  -- Since the list has only one element, there are no two different indices to compare, so the condition is trivially satisfied.
  simp [allDifferent];
  -- Since the list [42] has only one element, the length is 1. Therefore, for any i and j, if i < 1 and j < 1, then i must equal j.
  simp [test4_lst]

----------------------------
-- Verification: test6
----------------------------
lemma test6_precondition :
  precondition test6_lst := by
  exact?

lemma test6_postcondition :
  postcondition test6_lst test6_Expected := by
  -- For the list [5, 5], the result should be false because there are duplicates.
  simp [postcondition, test6_Expected];
  -- For the list [5, 5], the result should be false because there are duplicates. We need to show that both ensures1 and ensures2 hold.
  simp [ensures1, allDifferent];
  native_decide +revert

----------------------------
-- Verification: test13
----------------------------
lemma test13_precondition :
  precondition test13_lst := by
  exact?

lemma test13_postcondition :
  postcondition test13_lst test13_Expected := by
  -- Since the list has no duplicates, the result is true.
  have h_test13_true : allDifferent test13_lst := by
    -- Since the list is constructed with distinct elements, the allDifferent condition holds.
    intros i j hi hj hij;
    -- Since the list is constructed with distinct elements, we can use the fact that the list is injective.
    have h_inj : List.Nodup test13_lst := by
      native_decide;
    have := List.nodup_iff_injective_get.mp h_inj; aesop;
    -- Apply the injectivity of `test13_lst.get` to derive that `i = j` from `a`, which contradicts `hij`.
    have := @this ⟨i, hi⟩ ⟨j, hj⟩; aesop;
  -- By definition of postcondition, we need to show that ensures1 and ensures2 hold.
  unfold postcondition ensures1;
  -- Since test13_Expected is true and allDifferent test13_lst is true, the first part of the conjunction holds.
  simp [h_test13_true, test13_Expected]

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (lst: List Int):
  precondition lst →
  (∀ ret1 ret2,
    postcondition lst ret1 →
    postcondition lst ret2 →
    ret1 = ret2) := by
  -- By definition of postcondition, if ret1 and ret2 both satisfy the postcondition, then they must both be true or both be false.
  intros h_precondition ret1 ret2 h_ret1 h_ret2
  have h_eq : ret1 = ret2 := by
    cases ret1 <;> cases ret2 <;> simp_all +decide only [postcondition];
    · unfold ensures1 at *; aesop;
    · unfold ensures1 at *; aesop;
  -- Since $ret1 = ret2$ by hypothesis, we can conclude the proof.
  apply h_eq
