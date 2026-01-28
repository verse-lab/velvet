import Lean
import Mathlib.Tactic

-- Helper Functions

def dominoTilingRecurrence (n: Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 0
  | n + 4 => 4 * dominoTilingRecurrence (n + 2) - dominoTilingRecurrence n

def ensures1 (n : Nat) (count : Nat) :=
  count = dominoTilingRecurrence n  -- For even n≥4, follows recurrence relation

def precondition (n: Nat) :=
  True

def postcondition (n: Nat) (count: Nat) :=
  ensures1 n count

-- Test Cases
def test1_n : Nat := 2

def test1_Expected : Nat := 3

def test3_n : Nat := 1

def test3_Expected : Nat := 0

def test5_n : Nat := 5

def test5_Expected : Nat := 0

def test6_n : Nat := 7

def test6_Expected : Nat := 0

def test7_n : Nat := 4

def test7_Expected : Nat := 11

def test8_n : Nat := 6

def test8_Expected : Nat := 41

-------------------------------
-- Verifications
-------------------------------

-- test1
lemma test1_precondition :
  precondition test1_n := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test1_postcondition :
  postcondition test1_n test1_Expected := by
  -- Let's verify each part of the postcondition for test1.
  simp [test1_n, test1_Expected, postcondition, ensures1, dominoTilingRecurrence]

-- test3
lemma test3_precondition :
  precondition test3_n := by
  -- The precondition is trivially true for any n.
  trivial

lemma test3_postcondition :
  postcondition test3_n test3_Expected := by
  -- Let's verify each part of the postcondition for n = 3 and count = 0.
  constructor;

-- test5
lemma test5_precondition :
  precondition test5_n := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test5_postcondition :
  postcondition test5_n test5_Expected := by
  constructor

-- test6
lemma test6_precondition :
  precondition test6_n := by
  -- The precondition for test6_n is True, so it is trivially satisfied.
  simp [precondition]

lemma test6_postcondition :
  postcondition test6_n test6_Expected := by
  constructor

-- test7
lemma test7_precondition :
  precondition test7_n := by
  exact?

lemma test7_postcondition :
  postcondition test7_n test7_Expected := by
  constructor

-- test8
lemma test8_precondition :
  precondition test8_n := by
  -- The precondition is always true, so we can use the fact that True is true.
  simp [precondition]

lemma test8_postcondition :
  postcondition test8_n test8_Expected := by
  constructor

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (n: Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  unfold postcondition ensures1 at * ; aesop;
