import Lean
import Mathlib.Tactic

-- Helper Functions

def factorial (n: Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def lastDigit (n: Nat) : Nat :=
  n % 10

def factorialQuotient (a b: Nat) : Nat :=
  factorial b / factorial a

-- Postcondition clauses

def ensures1 (a : Nat) (b : Nat) (result : Nat) :=
  result = lastDigit (factorialQuotient a b)
def ensures2 (a : Nat) (b : Nat) (result : Nat) :=
  result < 10

def precondition (a: Nat) (b: Nat) :=
  True

def postcondition (a: Nat) (b: Nat) (result: Nat) :=
  ensures1 a b result ∧ ensures2 a b result

-- Test Cases
def test1_a : Nat := 2

def test1_b : Nat := 4

def test1_Expected : Nat := 2

def test2_a : Nat := 5

def test2_b : Nat := 5

def test2_Expected : Nat := 1

def test3_a : Nat := 0

def test3_b : Nat := 3

def test3_Expected : Nat := 6

def test5_a : Nat := 3

def test5_b : Nat := 5

def test5_Expected : Nat := 0

def test7_a : Nat := 4

def test7_b : Nat := 5

def test7_Expected : Nat := 5

def test9_a : Nat := 1

def test9_b : Nat := 4

def test9_Expected : Nat := 4

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_a test1_b := by
  trivial

lemma test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  -- Let's verify the test case for a=2 and b=4.
  -- We need to check if the last digit of the quotient is 2.
  unfold postcondition
  aesop;
  -- Let's calculate the last digit of the quotient of the factorial of 4 divided by the factorial of 2.
  simp [ensures2, test1_Expected]

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_a test2_b := by
  trivial

lemma test2_postcondition :
  postcondition test2_a test2_b test2_Expected := by
  -- Let's simplify the goal for test2.
  simp [postcondition];
  -- Let's simplify the goal for test2 and verify the conditions.
  simp +decide [ensures1, ensures2]

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_a test3_b := by
  trivial

lemma test3_postcondition :
  postcondition test3_a test3_b test3_Expected := by
  -- Let's calculate the factorial quotient and its last digit for the test case.
  have h_factorial_quotient : factorialQuotient 0 3 = 6 := by
    -- By definition of factorial, we know that 3! = 6 and 0! = 1.
    have h_factorial : factorial 3 = 6 ∧ factorial 0 = 1 := by
      -- We can prove this by definition.
      simp [factorial];
    unfold factorialQuotient
    simp [h_factorial];
  -- Since 6 is the last digit and it's less than 10, the postcondition holds.
  simp [h_factorial_quotient, postcondition];
  -- We'll use that 6 is the last digit of 6 and that 6 is less than 10.
  simp [ensures1, ensures2];
  native_decide +revert

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_a test5_b := by
  trivial

lemma test5_postcondition :
  postcondition test5_a test5_b test5_Expected := by
  -- By definition of factorialQuotient, we know that factorialQuotient 3 5 = 5! / 3! = 120 / 6 = 20.
  have h_factorialQuotient : factorialQuotient 3 5 = 20 := by
    -- By definition of factorialQuotient, we have factorialQuotient 3 5 = factorial 5 / factorial 3.
    simp [factorialQuotient, factorial];
  -- By definition of postcondition, we need to show that the last digit of 20 is 0 and that it's less than 10.
  simp [postcondition, h_factorialQuotient];
  -- By definition of ensures1 and ensures2, we need to show that the last digit of 20 is 0 and that it's less than 10.
  simp [ensures1, ensures2, h_factorialQuotient];
  native_decide +revert

----------------------------
-- Verification: test7
----------------------------
lemma test7_precondition :
  precondition test7_a test7_b := by
  trivial

lemma test7_postcondition :
  postcondition test7_a test7_b test7_Expected := by
  constructor;
  · bound;
  · -- Since 5 is less than 10, we can conclude that the last digit is indeed less than 10.
    norm_num [ensures2];
    decide

----------------------------
-- Verification: test9
----------------------------
lemma test9_precondition :
  precondition test9_a test9_b := by
  trivial

lemma test9_postcondition :
  postcondition test9_a test9_b test9_Expected := by
  -- Now let's verify that the result is indeed the last digit of the quotient.
  apply And.intro;
  · exact?;
  · -- The last digit of 24 is 4.
    norm_num [test9_Expected];
    -- The last digit of 24 is 4, so the postcondition holds.
    simp [ensures2]

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (a: Nat) (b: Nat):
  precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  unfold postcondition at *; aesop;
  unfold ensures1 at *; unfold ensures2 at *; aesop;
