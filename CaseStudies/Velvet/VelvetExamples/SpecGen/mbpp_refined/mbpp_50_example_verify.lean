import Lean
import Mathlib.Tactic

-- Helper Functions

def findFirstIndex (lists : List (List Nat)) (len : Nat) : Option Nat :=
  lists.findIdx? (fun l => l.length = len)

def isFirstWithLength (lists : List (List Nat)) (target : List Nat) (len : Nat) : Prop :=
  target ∈ lists ∧ target.length = len ∧
  (∀ i < lists.length, lists[i]!.length = len →
    ∃ j ≤ i, j < lists.length ∧ lists[j]! = target)

def require1 (lists : List (List Nat)) :=
  lists.length > 0

-- Postcondition clauses

def ensures1 (lists : List (List Nat)) (result : (Nat × List Nat)) :=
  result.2 ∈ lists
def ensures2 (lists : List (List Nat)) (result : (Nat × List Nat)) :=
  result.2.length = result.1
def ensures3 (lists : List (List Nat)) (result : (Nat × List Nat)) :=
  ∀ other ∈ lists, result.1 ≤ other.length
def ensures4 (lists : List (List Nat)) (result : (Nat × List Nat)) :=
  isFirstWithLength lists result.2 result.1

def precondition (lists: List (List Nat)) :=
  require1 lists

def postcondition (lists: List (List Nat)) (result: (Nat × List Nat)) :=
  ensures1 lists result ∧ ensures2 lists result ∧ ensures3 lists result ∧ ensures4 lists result

-- Test Cases
def test1_lists : List (List Nat) := [[0], [1, 3], [5, 7], [9, 11], [13, 15, 17]]

def test1_Expected : (Nat × List Nat) := (1, [0])

def test2_lists : List (List Nat) := [[1,2,3,4,5], [1,2,3,4], [1,2,3], [1,2], [1]]

def test2_Expected : (Nat × List Nat) := (1, [1])

def test3_lists : List (List Nat) := [[3,4,5], [6,7,8,9], [10,11,12], [1,2]]

def test3_Expected : (Nat × List Nat) := (2, [1,2])

def test4_lists : List (List Nat) := [[1,2,3], [], [4,5]]

def test4_Expected : (Nat × List Nat) := (0, [])

def test5_lists : List (List Nat) := [[1,2,3,4,5]]

def test5_Expected : (Nat × List Nat) := (5, [1,2,3,4,5])

def test8_lists : List (List Nat) := [[1,2,3], [4], [5], [6,7]]

def test8_Expected : (Nat × List Nat) := (1, [4])

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_lists := by
  exact Nat.succ_pos _

lemma test1_postcondition :
  postcondition test1_lists test1_Expected := by
  -- Check that the result satisfies the postcondition.
  simp [postcondition];
  -- Check that the result satisfies the postcondition for test1.
  simp [ensures1, ensures2, ensures3, ensures4];
  -- Check that [0] is in the list and has length 1.
  simp [isFirstWithLength];
  native_decide +revert

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_lists := by
  exact Nat.zero_lt_succ _

lemma test2_postcondition :
  postcondition test2_lists test2_Expected := by
  unfold postcondition; aesop;
  · exact by tauto;
  · -- We need to show that the length of the list [1] is less than or equal to the length of any other list in the collection.
    simp [ensures3, test2_lists, test2_Expected];
  · -- Let's unfold the definition of `ensures4`.
    unfold ensures4;
    -- Show that [1] is in the list and is the first occurrence of a list with length 1.
    simp [isFirstWithLength, test2_lists, test2_Expected];
    -- By examining each case, we can see that the only i that satisfies the condition is 4.
    intro i hi h_len
    interval_cases i <;> simp_all +decide

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_lists := by
  -- The length of test3_lists is 4, which is greater than 0.
  simp [test3_lists];
  -- The length of the list is 4, which is greater than 0.
  simp [precondition, require1]

lemma test3_postcondition :
  postcondition test3_lists test3_Expected := by
  -- Check if the result is in the list.
  simp [postcondition, test3_lists, test3_Expected];
  -- Let's verify each condition step by step.
  simp [ensures1, ensures2, ensures3, ensures4];
  -- Show that [1, 2] is the first list with length 2.
  simp [isFirstWithLength];
  -- We can check each case individually since i is less than 4.
  intro i hi hlength
  interval_cases i <;> simp_all +decide

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_lists := by
  -- Check that the input list is non-empty.
  apply List.length_pos_of_ne_nil
  simp [test4_lists]

lemma test4_postcondition :
  postcondition test4_lists test4_Expected := by
  -- Let's verify each part of the postcondition for test4_lists and test4_Expected.
  simp [postcondition, ensures1, ensures2, ensures3, ensures4];
  -- Let's verify that the empty list is indeed the first element in test4_lists.
  simp [test4_Expected, test4_lists, isFirstWithLength];
  decide +revert

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_lists := by
  exact Nat.succ_pos _

lemma test5_postcondition :
  postcondition test5_lists test5_Expected := by
  -- Let's verify each part of the postcondition for test5_lists and test5_Expected.
  apply And.intro;
  · -- Show that the second component of the result is in the input list.
    apply List.mem_singleton_self;
  · -- Let's unfold the definition of `isFirstWithLength` to verify the postcondition.
    unfold ensures2 ensures3 ensures4;
    exact ⟨ rfl, by native_decide, by unfold isFirstWithLength; native_decide ⟩

----------------------------
-- Verification: test8
----------------------------
lemma test8_precondition :
  precondition test8_lists := by
  -- The length of the list `test8_lists` is 4, which is greater than 0.
  simp [precondition, test8_lists];
  -- The length of the list is 4, which is greater than 0.
  simp [require1]

lemma test8_postcondition :
  postcondition test8_lists test8_Expected := by
  -- Let's verify each part of the postcondition for test8.
  apply And.intro;
  · -- We need to show that [4] is indeed an element of the list of lists.
    simp [test8_lists, test8_Expected];
    -- The list [4] is indeed in the input list.
    simp [ensures1];
  · -- Verify that the expected result satisfies the second part of the postcondition.
    apply And.intro;
    · -- The length of the second element in the expected result is 1, which matches the first element.
      simp [ensures2, test8_Expected];
    · -- Verify that the expected result satisfies the third part of the postcondition.
      apply And.intro;
      · -- Check that the expected result's first element is the length of the list.
        simp [ensures3];
        native_decide;
      · constructor <;> norm_cast

-----------------------------
-- Uniqueness Verification --
-----------------------------

set_option maxHeartbeats 1000000

lemma uniqueness (lists: List (List Nat)):
  precondition lists →
  (∀ ret1 ret2,
    postcondition lists ret1 →
    postcondition lists ret2 →
    ret1 = ret2) := by
  -- By definition of postcondition, if ret1 and ret2 are both valid, they must have the same length and be the first occurrence of that length.
  intros h_pre ret1 ret2 h_ret1 h_ret2
  have h_len : ret1.1 = ret2.1 := by
    -- Since both ret1 and ret2 are valid, their lengths must be the minimum length in the list.
    have h_min : ∀ l ∈ lists, ret1.1 ≤ l.length ∧ ret2.1 ≤ l.length := by
      exact fun l hl => ⟨ h_ret1.2.2.1 l hl, h_ret2.2.2.1 l hl ⟩;
    refine' le_antisymm _ _ <;> aesop;
    · -- Since fst is the minimum length, it must be less than or equal to any other length in the collection, including fst_1.
      have h_fst_le_fst1 : fst ≤ snd_1.length := by
        exact h_min _ h_ret2.1 |>.1;
      have := h_ret2.2.1; aesop;
      exact?;
    · have := h_ret1.2.2.2;
      cases this ; aesop;
  bound;
  -- Since snd and snd_1 are both the first occurrence of the length fst, their indices in the lists must be the same.
  have h_index : snd ∈ lists ∧ snd_1 ∈ lists ∧ snd.length = fst ∧ snd_1.length = fst ∧ (∀ i < lists.length, lists[i]!.length = fst → ∃ j ≤ i, j < lists.length ∧ lists[j]! = snd) ∧ (∀ i < lists.length, lists[i]!.length = fst → ∃ j ≤ i, j < lists.length ∧ lists[j]! = snd_1) := by
    unfold postcondition at *; aesop;
    · unfold ensures4 at *; aesop;
      unfold isFirstWithLength at *; aesop;
    · unfold ensures4 at *; aesop;
      unfold isFirstWithLength at *; aesop;
  obtain ⟨i, hi⟩ : ∃ i < lists.length, lists[i]! = snd := by
    -- Since snd is in the lists, by the definition of list membership, there must be some index i where lists[i]! = snd.
    have h_exists_i : ∃ i, i < lists.length ∧ lists[i]! = snd := by
      have h_mem : snd ∈ lists := h_index.1
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 h_mem; use i; aesop;
    exact h_exists_i
  obtain ⟨j, hj⟩ : ∃ j < lists.length, lists[j]! = snd_1 := by
    grind;
  obtain ⟨k, hk⟩ : ∃ k < lists.length, lists[k]! = snd_1 ∧ ∀ m < k, ¬(lists[m]! = snd_1) := by
    exact ⟨ Nat.find ( ⟨ j, hj.1, hj.2 ⟩ : ∃ k < lists.length, lists[k]! = snd_1 ), Nat.find_spec ( ⟨ j, hj.1, hj.2 ⟩ : ∃ k < lists.length, lists[k]! = snd_1 ) |>.1, Nat.find_spec ( ⟨ j, hj.1, hj.2 ⟩ : ∃ k < lists.length, lists[k]! = snd_1 ) |>.2, fun m mn => fun h => not_lt_of_ge ( Nat.find_min' ( ⟨ j, hj.1, hj.2 ⟩ : ∃ k < lists.length, lists[k]! = snd_1 ) ⟨ by linarith [ Nat.find_spec ( ⟨ j, hj.1, hj.2 ⟩ : ∃ k < lists.length, lists[k]! = snd_1 ) |>.1 ], h ⟩ ) mn ⟩;
  grind
