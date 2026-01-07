import Lean
import Mathlib.Tactic

set_option maxHeartbeats 300000

-- Helper Functions

def countElem (list : List Nat) (elem : Nat) : Nat :=
  list.count elem

def firstIndex (list : List Nat) (elem : Nat) : Nat :=
  match list.findIdx? (· = elem) with
  | some idx => idx
  | none => list.length

def isSortedByCountAndOccurrence (flatList : List Nat) (result : List (Nat × Nat)) : Prop :=
  ∀ i j, i < j → j < result.length →
    let vi := result[i]!.1
    let vj := result[j]!.1
    let fi := result[i]!.2
    let fj := result[j]!.2
    let idxi := firstIndex flatList vi
    let idxj := firstIndex flatList vj
    (fi > fj) ∨ (fi = fj ∧ idxi < idxj)

-- Postcondition clauses
def ensures1 (lists : List (List Nat)) (result : List (Nat × Nat)) :=
  (∀ p ∈ result, p.2 = countElem lists.flatten p.1)

def ensures2 (lists : List (List Nat)) (result : List (Nat × Nat)) :=
  (∀ elem ∈ lists.flatten, ∃! p ∈ result, p.1 = elem) ∧
  (∀ p ∈ result, p.1 ∈ lists.flatten)

def ensures3 (lists : List (List Nat)) (result : List (Nat × Nat)) :=
  isSortedByCountAndOccurrence lists.flatten result

def precondition (lists: List (List Nat)) :=
  True

def postcondition (lists: List (List Nat)) (result: List (Nat × Nat)) :=
  ensures1 lists result ∧ ensures2 lists result ∧ ensures3 lists result

-- Test Cases
def test1_lists : List (List Nat) := [[1, 2, 3, 2], [4, 5, 6, 2], [7, 1, 9, 5]]

def test1_Expected : List (Nat × Nat) := [(2, 3), (1, 2), (5, 2), (3, 1), (4, 1), (6, 1), (7, 1), (9, 1)]

def test2_lists : List (List Nat) := []

def test2_Expected : List (Nat × Nat) := []

def test3_lists : List (List Nat) := [[42]]

def test3_Expected : List (Nat × Nat) := [(42, 1)]

def test5_lists : List (List Nat) := [[1, 2], [2, 3], [3, 1]]

def test5_Expected : List (Nat × Nat) := [(1, 2), (2, 2), (3, 2)]

def test9_lists : List (List Nat) := [[10, 20, 30], [10, 20], [10]]

def test9_Expected : List (Nat × Nat) := [(10, 3), (20, 2), (30, 1)]

def test11_lists : List (List Nat) := [[3, 1, 2], [1, 3], [2], [4, 5]]

def test11_Expected : List (Nat × Nat) := [(3, 2), (1, 2), (2, 2), (4, 1), (5, 1)]

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_lists := by
  exact?

lemma test1_postcondition :
  postcondition test1_lists test1_Expected := by
  -- By definition of `postcondition`, we need to show that `test1_Expected` satisfies `ensures1`, `ensures2`, and `ensures3`.
  unfold postcondition;
  -- Let's unfold the definitions of `ensures1`, `ensures2`, and `ensures3` to verify each condition.
  unfold ensures1 ensures2 ensures3;
  -- Let's verify the first part of the postcondition: ensures1.
  apply And.intro;
  · native_decide;
  · -- Let's verify the second part of the postcondition: ensures2 and ensures3.
    apply And.intro;
    · unfold test1_Expected test1_lists; simp +decide [ ExistsUnique ] ;
    · -- Let's verify the third part of the postcondition: ensures3.
      intro i j hij hj
      simp [test1_lists, test1_Expected] at *;
      interval_cases j <;> interval_cases i <;> trivial

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_lists := by
  exact?

lemma test2_postcondition :
  postcondition test2_lists test2_Expected := by
  -- Since the input list is empty, the postcondition is trivially satisfied.
  simp [postcondition];
  -- Since the input list is empty, the result list is also empty, satisfying all conditions.
  simp [test2_lists, test2_Expected, ensures1, ensures2, ensures3];
  -- The empty list is trivially sorted by count and occurrence.
  simp [isSortedByCountAndOccurrence];

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_lists := by
  -- The precondition for `test3_lists` is trivially true.
  exact trivial

lemma test3_postcondition :
  postcondition test3_lists test3_Expected := by
  -- Let's verify the postcondition for the test case where the input is a single list with one element.
  simp [postcondition, test3_lists, test3_Expected];
  -- Let's verify the postcondition for the test case where the input is a single list with one element, [[42]].
  simp [ensures1, ensures2, ensures3];
  -- Let's verify the postcondition for the test case where the input is a single element list, specifically [42].
  simp [countElem, isSortedByCountAndOccurrence];
  -- The only element in the list [42] is 42 itself, so the count is 1.
  simp [ExistsUnique];
  aesop

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_lists := by
  trivial

lemma test5_postcondition :
  postcondition test5_lists test5_Expected := by
  constructor;
  · -- Let's verify that each element in the result has the correct count.
    simp [ensures1, test5_lists, test5_Expected];
    decide;
  · unfold ensures2 ensures3;
    unfold isSortedByCountAndOccurrence; simp +decide ;
    rintro ( _ | _ | _ | _ | _ | i ) ( _ | _ | _ | _ | _ | j ) <;> simp +arith +decide;
    all_goals simp +arith +decide [ test5_Expected ]

----------------------------
-- Verification: test9
----------------------------
lemma test9_precondition :
  precondition test9_lists := by
  trivial

lemma test9_postcondition :
  postcondition test9_lists test9_Expected := by
  -- Now let's verify that the result list satisfies the postcondition for test9.
  unfold postcondition
  simp +decide [test9_lists, test9_Expected];
  -- Let's verify each part of the postcondition.
  constructor;
  · -- Let's verify that the result list satisfies the first part of the postcondition: for every pair (elem, count) in the result list, count is equal to the number of times elem appears in the flattened list.
    intro p hp
    aesop;
  · unfold ensures2 ensures3;
    unfold isSortedByCountAndOccurrence; simp +decide ;
    intro i j hij hj; interval_cases j <;> interval_cases i <;> trivial;

----------------------------
-- Verification: test11
----------------------------
lemma test11_precondition :
  precondition test11_lists := by
  exact?

lemma test11_postcondition :
  postcondition test11_lists test11_Expected := by
  -- Now let's verify the postcondition for test11.
  constructor;
  · -- Let's verify that the counts in the result match the actual counts in the flattened list for the test11 case.
    simp [ensures1, test11_lists, test11_Expected];
    native_decide;
  · unfold ensures2 ensures3;
    -- Let's verify that the result list is sorted by count in descending order and by appearance in the flattened list in ascending order for each element.
    constructor;
    · decide +kernel;
    · -- Now let's verify the third condition: the list is sorted by frequency and occurrence.
      intros i j hij hj
      simp [test11_lists, test11_Expected] at *;
      -- Let's check each possible pair (i, j) where i < j and j < 5.
      interval_cases j <;> interval_cases i <;> simp +decide

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (lists: List (List Nat)):
  precondition lists →
  (∀ ret1 ret2,
    postcondition lists ret1 →
    postcondition lists ret2 →
    ret1 = ret2) := by
  rintro - ret1 ret2 ⟨ h1, h2, h3 ⟩ ⟨ h4, h5, h6 ⟩;
  -- Since both ret1 and ret2 are sorted by count and occurrence, and they have the same elements, they must be identical.
  have h_sorted_unique : ∀ (l1 l2 : List (ℕ × ℕ)), List.Sorted (fun p q => p.2 > q.2 ∨ (p.2 = q.2 ∧ firstIndex (lists.flatten) p.1 < firstIndex (lists.flatten) q.1)) l1 → List.Sorted (fun p q => p.2 > q.2 ∨ (p.2 = q.2 ∧ firstIndex (lists.flatten) p.1 < firstIndex (lists.flatten) q.1)) l2 → (∀ p ∈ l1, p ∈ l2) → (∀ p ∈ l2, p ∈ l1) → l1 = l2 := by
    intros l1 l2 hl1 hl2 h1 h2;
    induction' l1 with p l1 ih generalizing l2 <;> induction' l2 with q l2 ih' <;> simp_all +decide;
    · simpa using h1 p.1 p.2;
    · grind;
  apply h_sorted_unique;
  · refine' List.pairwise_iff_get.mpr _;
    intro i j hij; specialize h3 i j; aesop;
  · exact List.pairwise_iff_get.mpr fun i j hij => by simpa using h6 ( i : ℕ ) ( j : ℕ ) ( by simpa using hij ) ( by simp ) ;
  · intro p hp;
    unfold ensures2 at *;
    obtain ⟨ q, hq1, hq2 ⟩ := h5.1 p.1 ( h2.2 p hp );
    have := h1 p hp; have := h4 q hq1.1; aesop;
  · intro p hp;
    have := h5.2 p hp;
    have := h2.1 p.1;
    obtain ⟨ q, hq1, hq2 ⟩ := this ‹_›;
    have := h4 p hp; have := h1 q hq1.1; aesop;
