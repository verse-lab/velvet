import Lean
import Mathlib.Tactic

-- Helper Functions

def extractAt (lst : List Nat) (n : Nat) : Option Nat :=
  if n < lst.length then lst[n]? else none

def filterMapExtract (lists : List (List Nat)) (n : Nat) : List Nat :=
  lists.filterMap (fun sublist => extractAt sublist n)

def ensures1 (lists : List (List Nat)) (n : Nat) (result : List Nat) :=
  result = filterMapExtract lists n

def precondition (lists: List (List Nat)) (n: Nat) :=
  True

def postcondition (lists: List (List Nat)) (n: Nat) (result: List Nat) :=
  ensures1 lists n result

-- Test Cases
def test1_lists : List (List Nat) := [[1, 2, 3], [4, 5], [6, 7, 8, 9]]

def test1_n : Nat := 1

def test1_Expected : List Nat := [2, 5, 7]

def test3_lists : List (List Nat) := [[1, 2], [3], [4, 5, 6]]

def test3_n : Nat := 2

def test3_Expected : List Nat := [6]

def test4_lists : List (List Nat) := [[1], [2], [3]]

def test4_n : Nat := 1

def test4_Expected : List Nat := []

def test5_lists : List (List Nat) := []

def test5_n : Nat := 0

def test5_Expected : List Nat := []

def test6_lists : List (List Nat) := [[], [1, 2, 3], [], [4, 5]]

def test6_n : Nat := 1

def test6_Expected : List Nat := [2, 5]

def test9_lists : List (List Nat) := [[1, 2], [3, 4], [5, 6]]

def test9_n : Nat := 1

def test9_Expected : List Nat := [2, 4, 6]

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_lists test1_n := by
  exact?

lemma test1_postcondition :
  postcondition test1_lists test1_n test1_Expected := by
  -- Apply the definition of `postcondition` to conclude the proof.
  apply Eq.refl

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_lists test3_n := by
  exact?

lemma test3_postcondition :
  postcondition test3_lists test3_n test3_Expected := by
  exact?

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_lists test4_n := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test4_postcondition :
  postcondition test4_lists test4_n test4_Expected := by
  -- By definition of `postcondition`, we need to show that `test4_Expected = filterMapExtract test4_lists test4_n`.
  simp [postcondition, filterMapExtract];
  -- By definition of `filterMapExtract`, we need to show that the result is equal to the filterMapExtract of the lists and n.
  simp [ensures1, filterMapExtract];
  decide +kernel

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_lists test5_n := by
  exact?

lemma test5_postcondition :
  postcondition test5_lists test5_n test5_Expected := by
  -- Since the list is empty, the result of filterMapExtract is also empty.
  simp [postcondition, test5_lists, test5_n, test5_Expected];
  -- Since the list is empty, the result of filterMapExtract is also empty. Therefore, the postcondition holds.
  simp [ensures1, filterMapExtract]

----------------------------
-- Verification: test6
----------------------------
lemma test6_precondition :
  precondition test6_lists test6_n := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test6_postcondition :
  postcondition test6_lists test6_n test6_Expected := by
  -- Apply the filterMapExtract function with the given lists and n.
  apply Eq.refl

----------------------------
-- Verification: test9
----------------------------
lemma test9_precondition :
  precondition test9_lists test9_n := by
  trivial

lemma test9_postcondition :
  postcondition test9_lists test9_n test9_Expected := by
  exact?

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (lists: List (List Nat)) (n: Nat):
  precondition lists n →
  (∀ ret1 ret2,
    postcondition lists n ret1 →
    postcondition lists n ret2 →
    ret1 = ret2) := by
  -- By definition of postcondition, if both ret1 and ret2 satisfy the postcondition, they must both be equal to the same filterMapExtract.
  intros h_pre ret1 ret2 h_ret1 h_ret2
  rw [h_ret1, h_ret2]
