import Lean
import Mathlib.Tactic

def ensures1 (n : Nat) (m : Nat) (multiples : Array Nat) :=
  multiples.size = m  -- The result contains exactly m elements
def ensures2 (n : Nat) (m : Nat) (multiples : Array Nat) :=
  ∀ i, i < m → multiples[i]! = (i + 1) * n  -- Each element is the (i+1)-th multiple of n

def precondition (n: Nat) (m: Nat) :=
  True

def postcondition (n: Nat) (m: Nat) (multiples: Array Nat) :=
  ensures1 n m multiples ∧ ensures2 n m multiples

-- Test Cases
def test1_n : Nat := 3
def test1_m : Nat := 5
def test1_Expected : Array Nat := #[3, 6, 9, 12, 15]
def test2_n : Nat := 7
def test2_m : Nat := 0
def test2_Expected : Array Nat := #[]
def test3_n : Nat := 10
def test3_m : Nat := 1
def test3_Expected : Array Nat := #[10]
def test4_n : Nat := 0
def test4_m : Nat := 4
def test4_Expected : Array Nat := #[0, 0, 0, 0]
def test6_n : Nat := 50
def test6_m : Nat := 3
def test6_Expected : Array Nat := #[50, 100, 150]
def test7_n : Nat := 2
def test7_m : Nat := 10
def test7_Expected : Array Nat :=
  #[2, 4, 6, 8, 10, 12, 14, 16, 18, 20]

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_n test1_m := by
  trivial

lemma test1_postcondition :
  postcondition test1_n test1_m test1_Expected := by
  simp [postcondition, ensures1, ensures2]
  trivial

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_n test2_m := by
  trivial

lemma test2_postcondition :
  postcondition test2_n test2_m test2_Expected := by
  simp [postcondition, ensures1, ensures2]
  trivial

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_n test3_m := by
  trivial

lemma test3_postcondition :
  postcondition test3_n test3_m test3_Expected := by
  simp [postcondition, ensures1, ensures2]
  trivial

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_n test4_m := by
  trivial

lemma test4_postcondition :
  postcondition test4_n test4_m test4_Expected := by
  simp [postcondition, ensures1, ensures2]
  trivial

----------------------------
-- Verification: test6
----------------------------
lemma test6_precondition :
  precondition test6_n test6_m := by
  trivial

lemma test6_postcondition :
  postcondition test6_n test6_m test6_Expected := by
  simp [postcondition, ensures1, ensures2]
  trivial

----------------------------
-- Verification: test7
----------------------------
lemma test7_precondition :
  precondition test7_n test7_m := by
  trivial

lemma test7_postcondition :
  postcondition test7_n test7_m test7_Expected := by
  simp [postcondition, ensures1, ensures2]
  trivial

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (n: Nat) (m: Nat):
  precondition n m →
  (∀ ret1 ret2,
    postcondition n m ret1 →
    postcondition n m ret2 →
    ret1 = ret2) := by
  simp [precondition, postcondition, ensures1, ensures2]
  intros ret1 ret2 hs1 hret1 hs2 hret2
  apply Array.ext_iff.2
  grind
