import Lean
import Mathlib.Tactic

-- Helper Functions

def ensures1 (n : Nat) (result : Nat) :=
  result = n * (n + 1)

def precondition (n: Nat) :=
  True

def postcondition (n: Nat) (result: Nat) :=
  ensures1 n result

-- Test Cases
def test0_n : Nat := 4

def test0_Expected : Nat := 20

def test1_n : Nat := 0

def test1_Expected : Nat := 0

def test2_n : Nat := 1

def test2_Expected : Nat := 2

def test5_n : Nat := 5

def test5_Expected : Nat := 30

def test9_n : Nat := 50

def test9_Expected : Nat := 2550

def test14_n : Nat := 1000

def test14_Expected : Nat := 1001000

-------------------------------
-- Verifications
-------------------------------

-- test0
lemma test0_precondition :
  precondition test0_n := by
  -- The precondition is trivially true for any n.
  simp [precondition]

lemma test0_postcondition :
  postcondition test0_n test0_Expected := by
  -- Let's verify each part of the postcondition for the test case where n is 4.
  simp [postcondition, ensures1];
  -- Let's simplify the goal.
  simp [test0_n, test0_Expected];

-- test1
lemma test1_precondition :
  precondition test1_n := by
  -- The precondition is trivially true for any input.
  simp [precondition]

lemma test1_postcondition :
  postcondition test1_n test1_Expected := by
  -- For the test case where n is 0, we need to verify that the postcondition holds.
  simp [postcondition, ensures1];
  -- For the test case where n is 0, we need to verify that the postcondition holds. The postcondition is defined as the conjunction of three conditions: ensures1, ensures2, and ensures3.
  simp [test1_Expected, test1_n]

-- test2
lemma test2_precondition :
  precondition test2_n := by
  exact?

lemma test2_postcondition :
  postcondition test2_n test2_Expected := by
  -- Let's verify each part of the postcondition for test2_n and test2_Expected.
  simp [postcondition, ensures1];
  -- Let's verify each part of the postcondition for test2_n and test2_Expected. We'll start with ensures1.
  simp [test2_n, test2_Expected];

-- test5
lemma test5_precondition :
  precondition test5_n := by
  -- The precondition is trivially true.
  simp [precondition]

lemma test5_postcondition :
  postcondition test5_n test5_Expected := by
  -- We need to show that the computed value satisfies all the postconditions for n=5.
  simp [postcondition, test5_n, test5_Expected];
  -- We can verify each condition directly.
  simp [ensures1];

-- test9
lemma test9_precondition :
  precondition test9_n := by
  exact?

lemma test9_postcondition :
  postcondition test9_n test9_Expected := by
  -- By definition of `postcondition`, we need to show that `test9_Expected` satisfies the three properties.
  simp [postcondition, test9_n, test9_Expected];
  -- Let's verify each part of the conjunction.
  simp [ensures1];

-- test14
lemma test14_precondition :
  precondition test14_n := by
  -- The precondition is trivially satisfied since test14_n is a natural number.
  simp [precondition]

lemma test14_postcondition :
  postcondition test14_n test14_Expected := by
  -- By definition of postcondition, we need to show that ensures1, ensures2, and ensures3 hold for n=1000 and result=1001000.
  simp [postcondition, ensures1];
  -- Let's verify each part of the postcondition for the test case where n is 1000.
  simp [test14_n, test14_Expected];

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (n: Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro h
  rintro ret1 ret2 ⟨h1, h2⟩ ⟨h3, h4⟩
  aesop;
