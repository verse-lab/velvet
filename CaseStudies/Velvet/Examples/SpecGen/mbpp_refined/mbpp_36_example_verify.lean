import Lean
import Mathlib.Tactic

-- Helper Functions

def nthDecimalDigit (numerator: Nat) (denominator: Nat) (n: Nat) : Nat :=
  if denominator = 0 then 0  -- guard against division by zero
  else ((numerator * (10 ^ n)) / denominator) % 10

def require1 (numerator : Nat) (denominator : Nat) (n : Nat) :=
  numerator < denominator  -- proper fraction constraint
def require2 (numerator : Nat) (denominator : Nat) (n : Nat) :=
  denominator > 0  -- cannot divide by zero
def require3 (numerator : Nat) (denominator : Nat) (n : Nat) :=
  n ≥ 1  -- n is 1-indexed (first digit is at position 1)

-- Postcondition clauses

def ensures1 (numerator : Nat) (denominator : Nat) (n : Nat) (digit : Nat) :=
  digit = nthDecimalDigit numerator denominator n  -- the result is the nth decimal digit
def ensures2 (numerator : Nat) (denominator : Nat) (n : Nat) (digit : Nat) :=
  digit ≥ 0 ∧ digit ≤ 9  -- result is a valid decimal digit

def precondition (numerator: Nat) (denominator: Nat) (n: Nat) :=
  require1 numerator denominator n ∧ require2 numerator denominator n ∧ require3 numerator denominator n

def postcondition (numerator: Nat) (denominator: Nat) (n: Nat) (digit: Nat) :=
  ensures1 numerator denominator n digit ∧ ensures2 numerator denominator n digit

-- Test Cases
def test1_numerator : Nat := 1

def test1_denominator : Nat := 2

def test1_n : Nat := 1

def test1_Expected : Nat := 5

def test5_numerator : Nat := 1

def test5_denominator : Nat := 3

def test5_n : Nat := 5

def test5_Expected : Nat := 3

def test7_numerator : Nat := 2

def test7_denominator : Nat := 3

def test7_n : Nat := 3

def test7_Expected : Nat := 6

def test10_numerator : Nat := 1

def test10_denominator : Nat := 7

def test10_n : Nat := 4

def test10_Expected : Nat := 8

def test13_numerator : Nat := 3

def test13_denominator : Nat := 11

def test13_n : Nat := 3

def test13_Expected : Nat := 2

def test20_numerator : Nat := 47

def test20_denominator : Nat := 99

def test20_n : Nat := 10

def test20_Expected : Nat := 7

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_numerator test1_denominator test1_n := by
  -- Check that the numerator is less than the denominator.
  simp [precondition, require1, require2, require3];
  decide

lemma test1_postcondition :
  postcondition test1_numerator test1_denominator test1_n test1_Expected := by
  exact ⟨ by aesop, by trivial ⟩

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_numerator test5_denominator test5_n := by
  -- Check that the numerator is less than the denominator.
  have h1 : 1 < 3 := by
    norm_num;
  -- Check that the numerator is less than the denominator and the denominator is positive.
  apply And.intro h1
  simp [test5_denominator];
  aesop;
  · exact Nat.succ_pos _;
  · exact Nat.le_add_left _ _

lemma test5_postcondition :
  postcondition test5_numerator test5_denominator test5_n test5_Expected := by
  -- Calculate the 5th digit of the decimal expansion of 1/3, which is 3.
  norm_cast

----------------------------
-- Verification: test7
----------------------------
lemma test7_precondition :
  precondition test7_numerator test7_denominator test7_n := by
  -- Check that the numerator is less than the denominator.
  simp [precondition, test7_numerator, test7_denominator, test7_n];
  -- Check that the numerator is less than the denominator, the denominator is positive, and n is at least 1.
  simp [require1, require2, require3]

lemma test7_postcondition :
  postcondition test7_numerator test7_denominator test7_n test7_Expected := by
  -- By definition of `postcondition`, we need to show that `test7_Expected` is the nth decimal digit and that it's between 0 and 9.
  simp [postcondition, test7_numerator, test7_denominator, test7_n, test7_Expected];
  -- By definition of `nthDecimalDigit`, we have:
  simp [ensures1, ensures2, nthDecimalDigit]

----------------------------
-- Verification: test10
----------------------------
lemma test10_precondition :
  precondition test10_numerator test10_denominator test10_n := by
  simp [precondition, test10_numerator, test10_denominator, test10_n];
  simp [require1, require2, require3]

lemma test10_postcondition :
  postcondition test10_numerator test10_denominator test10_n test10_Expected := by
  -- Let's calculate the value of $22 \times 10^4 / 7$ to verify the 4th digit.
  norm_cast at *

----------------------------
-- Verification: test13
----------------------------
lemma test13_precondition :
  precondition test13_numerator test13_denominator test13_n := by
  constructor;
  · -- We need to show that the numerator is less than the denominator.
    simp [require1];
    -- We can prove this by using the fact that 3 is less than 11.
    norm_num [test13_numerator, test13_denominator];
  · -- Check that the denominator is greater than 0 and that n is at least 1.
    simp [require2, require3, test13_numerator, test13_denominator, test13_n]

lemma test13_postcondition :
  postcondition test13_numerator test13_denominator test13_n test13_Expected := by
  norm_cast

----------------------------
-- Verification: test20
----------------------------
lemma test20_precondition :
  precondition test20_numerator test20_denominator test20_n := by
  constructor;
  · exact Nat.lt_of_sub_eq_succ rfl;
  · -- Check that the denominator is positive.
    simp [require2, require3];
    exact ⟨ by decide, by decide ⟩

lemma test20_postcondition :
  postcondition test20_numerator test20_denominator test20_n test20_Expected := by
  -- Let's calculate the digit at the 10th position in the decimal expansion of 47/99.
  norm_num [postcondition];
  -- We need to show that the computed value is correct.
  simp +decide [ensures1, ensures2]

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (numerator: Nat) (denominator: Nat) (n: Nat):
  precondition numerator denominator n →
  (∀ ret1 ret2,
    postcondition numerator denominator n ret1 →
    postcondition numerator denominator n ret2 →
    ret1 = ret2) := by
  -- If two different results satisfy the postcondition, they must both be equal to the nth decimal digit. Hence, they must be equal to each other.
  intros h_pre ret1 ret2 h_ret1 h_ret2
  have h_eq : ret1 = nthDecimalDigit numerator denominator n ∧ ret2 = nthDecimalDigit numerator denominator n := by
    exact ⟨ h_ret1.1, h_ret2.1 ⟩;
  rw [ h_eq.left, h_eq.right ]
