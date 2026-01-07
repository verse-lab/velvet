import Lean
import Mathlib.Tactic

set_option maxRecDepth 10000

-- Helper Functions

def hasUniqueOddOccurrence (lst : List Nat) : Prop :=
  ∃! x, x ∈ lst ∧ lst.count x % 2 = 1
-- Predicate: an element is the unique odd-occurrence element

def isOddOccurrenceElement (lst : List Nat) (result: Nat) : Prop :=
  result ∈ lst ∧
  lst.count result % 2 = 1

def require1 (lst : List Nat) :=
  hasUniqueOddOccurrence lst

-- Postcondition clauses
def ensures1 (lst : List Nat) (result: Nat) :=
  isOddOccurrenceElement lst result

def precondition (lst: List Nat) :=
  require1 lst

def postcondition (lst: List Nat) (result: Nat) :=
  ensures1 lst result

-- Test Cases
def test0_Lst : List Nat := [5]

def test0_Expected : Nat := 5

def test3_Lst : List Nat := [2,3,5,4,5,2,4,3,5,2,4,4,2]

def test3_Expected : Nat := 5

def test7_Lst : List Nat := List.replicate 101 42 ++ List.replicate 100 13 ++ List.replicate 100 7

def test7_Expected : Nat := 42

def test10_Lst : List Nat := List.replicate 1000 10 ++ List.replicate 1000 20 ++ List.replicate 1000 30 ++ [999]

def test10_Expected : Nat := 999

def test14_Lst : List Nat := List.replicate 1001 77 ++ List.replicate 500 88 ++ List.replicate 500 99

def test14_Expected : Nat := 77

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test0
----------------------------
lemma test0_precondition :
  precondition test0_Lst := by
  -- In this case, the list `test0_Lst` contains only one element, which is 5.
  -- Since 5 appears exactly once in the list, it satisfies the condition of having a unique odd occurrence.
  use 5
  simp;
  native_decide +revert

lemma test0_postcondition :
  postcondition test0_Lst test0_Expected := by
  constructor;
  · simp [test0_Lst, test0_Expected];
  · simp [test0_Lst, test0_Expected]

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_Lst := by
  use 5
  simp;
  native_decide +revert

lemma test3_postcondition :
  postcondition test3_Lst test3_Expected := by
  constructor;
  · simp [test3_Lst, test3_Expected];
  · simp [test3_Lst, test3_Expected]

----------------------------
-- Verification: test7
----------------------------
lemma test7_precondition :
  precondition test7_Lst := by
  use 42
  simp;
  native_decide +revert

lemma test7_postcondition :
  postcondition test7_Lst test7_Expected := by
  -- We need to show that 42 is in the list, has an odd count, and is the only element with an odd count.
  apply And.intro;
  · decide +revert;
  · native_decide

----------------------------
-- Verification: test10
----------------------------
lemma test10_precondition :
  precondition test10_Lst := by
  use 999
  simp;
  native_decide +revert

lemma test10_postcondition :
  postcondition test10_Lst test10_Expected := by
  -- Verify that 999 is in the list and has an odd count.
  apply And.intro;
  · simp [test10_Lst, test10_Expected]
  · native_decide

----------------------------
-- Verification: test14
----------------------------
lemma test14_precondition :
  precondition test14_Lst := by
  use 77
  simp;
  native_decide +revert

lemma test14_postcondition :
  postcondition test14_Lst test14_Expected := by
  -- By definition of postcondition, we need to show that test14_Expected is in test14_Lst and that no other element in test14_Lst has an odd count.
  apply And.intro;
  · decide +revert;
  · native_decide +revert

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (lst: List Nat):
  precondition lst →
  (∀ ret1 ret2,
    postcondition lst ret1 →
    postcondition lst ret2 →
    ret1 = ret2) := by
  aesop;
  -- By definition of postcondition, if ret1 and ret2 both satisfy the postcondition, then they must be the unique element with an odd count.
  have h_unique : ∀ x, postcondition lst x → x = ret1 := by
    -- By the uniqueness part of the postcondition, if x satisfies the postcondition, then x must be equal to ret1.
    intros x hx
    simp [precondition, require1, hasUniqueOddOccurrence] at a
    obtain ⟨ x, hpre ⟩ := a
    simp [postcondition, ensures1, isOddOccurrenceElement] at *
    grind
  exact h_unique ret2 a_2 ▸ rfl
