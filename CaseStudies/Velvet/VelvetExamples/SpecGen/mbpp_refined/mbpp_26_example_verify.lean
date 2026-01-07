import Lean
import Mathlib.Tactic

-- Helper Functions

def allElementsEqualK (lst : List Nat) (k : Nat) : Prop :=
  ∀ elem ∈ lst, elem = k

def allListsHaveAllElementsK (lists : List (List Nat)) (k : Nat) : Prop :=
  ∀ lst ∈ lists, allElementsEqualK lst k

def ensures1 (lists : List (List Nat)) (k : Nat) (result : Bool) :=
  result = true ↔ allListsHaveAllElementsK lists k

def precondition (lists: List (List Nat)) (k: Nat) :=
  True

def postcondition (lists: List (List Nat)) (k: Nat) (result: Bool) :=
  ensures1 lists k result

-- Test Cases
def test1_lists : List (List Nat) := [[4, 4], [4, 4, 4], [4, 4], [4, 4, 4, 4], [4]]

def test1_k : Nat := 4

def test1_Expected : Bool := true

def test2_lists : List (List Nat) := [[3, 3], [3, 3], [3, 3]]

def test2_k : Nat := 3

def test2_Expected : Bool := true

def test3_lists : List (List Nat) := [[4, 4], [4, 5], [4, 4]]

def test3_k : Nat := 4

def test3_Expected : Bool := false

def test5_lists : List (List Nat) := [[2, 2], [], [2], []]

def test5_k : Nat := 2

def test5_Expected : Bool := true

def test8_lists : List (List Nat) := [[1], [1, 1, 1], [1, 1], [1, 1, 1, 1, 1]]

def test8_k : Nat := 1

def test8_Expected : Bool := true

def test13_lists : List (List Nat) := [[], [], []]

def test13_k : Nat := 100

def test13_Expected : Bool := true

-------------------------------
-- Verifications
-------------------------------

-- test1
lemma test1_precondition :
  precondition test1_lists test1_k := by
  exact?

lemma test1_postcondition :
  postcondition test1_lists test1_k test1_Expected := by
  -- Apply the definition of postcondition
  unfold postcondition;
  -- Apply the definition of `ensures1` to the specific lists and k value.
  simp [ensures1, test1_lists, test1_k, test1_Expected];
  -- We can verify each list individually to confirm that all elements are 4.
  simp [allListsHaveAllElementsK, allElementsEqualK]

-- test2
lemma test2_precondition :
  precondition test2_lists test2_k := by
  trivial

lemma test2_postcondition :
  postcondition test2_lists test2_k test2_Expected := by
  -- Since all elements in all lists are equal to 3, the condition holds.
  simp [postcondition, test2_lists, test2_k];
  -- Since all elements in all lists are equal to 3, the condition holds. We can use the fact that the lists are all 3s to conclude that the result is true.
  simp [ensures1, test2_Expected];
  -- We can verify each list individually.
  simp [allListsHaveAllElementsK, allElementsEqualK]

-- test3
lemma test3_precondition :
  precondition test3_lists test3_k := by
  trivial

lemma test3_postcondition :
  postcondition test3_lists test3_k test3_Expected := by
  -- Let's unfold the definition of `postcondition`.
  unfold postcondition;
  -- By definition of `test3_lists` and `test3_k`, we know that `test3_Expected` is true.
  simp [ensures1, test3_lists, test3_k];
  -- Let's unfold the definition of `allListsHaveAllElementsK`.
  unfold allListsHaveAllElementsK;
  -- Since the second list has a 5, the condition is false, so the equivalence holds.
  simp [test3_Expected, allElementsEqualK]

-- test5
lemma test5_precondition :
  precondition test5_lists test5_k := by
  -- The precondition is trivially true.
  simp [precondition]

lemma test5_postcondition :
  postcondition test5_lists test5_k test5_Expected := by
  -- By definition of `postcondition`, we need to show that `test5_Expected` is true if and only if all elements in all lists of `test5_lists` are equal to `test5_k`.
  simp [postcondition, test5_Expected, test5_lists, test5_k];
  -- By definition of `ensures1`, we need to show that `result = true ↔ allListsHaveAllElementsK lists k`.
  simp [ensures1];
  -- We can verify each list individually.
  simp [allListsHaveAllElementsK, allElementsEqualK]

-- test8
lemma test8_precondition :
  precondition test8_lists test8_k := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test8_postcondition :
  postcondition test8_lists test8_k test8_Expected := by
  -- Let's explicitly rewrite the definition of `postcondition` for this specific case.
  simp [postcondition, ensures1];
  -- Since all elements in each list of `test8_lists` are equal to `test8_k`, we can conclude that `allListsHaveAllElementsK` holds.
  simp [allListsHaveAllElementsK, allElementsEqualK];
  -- Since all elements in each list of `test8_lists` are equal to `test8_k`, we can conclude that `allListsHaveAllElementsK` holds. Therefore, the equivalence is true.
  simp [test8_Expected, test8_lists, test8_k]

-- test13
lemma test13_precondition :
  precondition test13_lists test13_k := by
  exact?

lemma test13_postcondition :
  postcondition test13_lists test13_k test13_Expected := by
  -- Apply the postcondition to the test case `test13` and show that it holds.
  unfold postcondition
  simp [test13_lists, test13_k, test13_Expected];
  -- Since the lists are all empty, the condition allElementsEqualK is vacuously true for each list. Therefore, the result is true.
  simp [ensures1, allListsHaveAllElementsK, allElementsEqualK]

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness(lists: List (List Nat)) (k: Nat):
  precondition lists k →
  (∀ ret1 ret2,
    postcondition lists k ret1 →
    postcondition lists k ret2 →
    ret1 = ret2) := by
  aesop;
  cases ret1 <;> cases ret2 <;> simp_all +decide [ postcondition ];
  · unfold ensures1 at * ; aesop;
  · unfold ensures1 at * ; aesop
