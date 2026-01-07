import Lean
import Mathlib.Tactic

-- Helper Functions

-- Helper function to check if all characters in string are '0' or '1'
def isValidBinaryStr (s: String) : Prop :=
  ∀ c ∈ s.toList, c = '0' ∨ c = '1'

def bitAt (s : String) (k : Nat) : Bool :=
  s.toList[s.length - 1 - k]! = '1'

def require1 (binary : String) :=
  isValidBinaryStr binary

-- Postcondition clauses
def ensures1 (binary : String) (decimal : Nat) :=
  ∀ k < binary.length,
    decimal.testBit k = bitAt binary k

def ensures2 (binary : String) (decimal : Nat) :=
  ∀ k ≥ binary.length,
    decimal.testBit k = false

def precondition (binary: String) :=
  require1 binary

def postcondition (binary: String) (decimal: Nat) :=
  ensures1 binary decimal ∧ ensures2 binary decimal

-- Test Cases
def test0_binary : String := "100"

def test0_Expected : Nat := 4

def test1_binary : String := "0"

def test1_Expected : Nat := 0

def test2_binary : String := "1"

def test2_Expected : Nat := 1

def test3_binary : String := "10"

def test3_Expected : Nat := 2

def test13_binary : String := "101010"

def test13_Expected : Nat := 42

def test18_binary : String := "1111111111"

def test18_Expected : Nat := 1023

def test19_binary : String := "10000000000"

def test19_Expected : Nat := 1024

-------------------------------
-- Verifications
-------------------------------

-- test0
lemma test0_precondition :
  precondition test0_binary := by
  -- We can verify that the string "100" consists only of '0' and '1' characters.
  have h_valid : ∀ c ∈ "100".toList, c = '0' ∨ c = '1' := by
    native_decide;
  -- Apply the hypothesis h_valid to conclude the proof.
  apply h_valid

lemma test0_postcondition :
  postcondition test0_binary test0_Expected := by
  -- Let's verify the postcondition for the test case 100.
  apply And.intro;
  · simp +decide [ ensures1 ];
  · intro k hk;
    rcases k with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> simp_all +decide [ Nat.testBit ];
    norm_num [ Nat.shiftRight_eq_div_pow ];
    norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul, test0_Expected ]

-- test1
lemma test1_precondition :
  precondition test1_binary := by
  -- The string "0" has only one character, which is '0', so the condition holds.
  simp [precondition, require1];
  -- Show that "0" is a valid binary string by applying the definition of `isValidBinaryStr`.
  simp [isValidBinaryStr, test1_binary]

lemma test1_postcondition :
  postcondition test1_binary test1_Expected := by
  -- Since the binary string "0" has no bits, both conditions are vacuously true.
  simp [postcondition, ensures1, ensures2];
  -- Since test1_binary is "0", its length is 1. Therefore, the first condition is vacuously true because there are no k less than 1.
  simp [test1_binary, test1_Expected];
  -- Since the length of "0" is 1, the only possible value for k is 0.
  simp [bitAt];
  -- Since the length of "0" is 1, the only possible value for k is 0. We need to show that the bit at position 0 is not '1'.
  simp [String.length]

-- test2
lemma test2_precondition :
  precondition test2_binary := by
  -- The binary string "1" is valid because it contains only the digit '1', which is either '0' or '1'.
  simp [require1, test2_binary];
  exact fun c hc => by rw [ String.toList ] at hc; aesop;

lemma test2_postcondition :
  postcondition test2_binary test2_Expected := by
  constructor;
  · -- For the binary string "1", the decimal equivalent is 1. We need to show that for all k < 1, the k-th bit of 1 is the same as the k-th bit of "1".
    simp [test2_binary, test2_Expected, ensures1];
    native_decide +revert;
  · -- For k ≥ 1, test2_Expected.testBit k is false because 1 in binary is 01, and the first bit is 1, but any higher bits are 0.
    intro k hk
    simp [Nat.testBit, hk];
    -- Since $k \geq 1$, we have $test2\_Expected >>> k = 0$.
    have h_shift : test2_Expected >>> k = 0 := by
      exact Nat.shiftRight_eq_div_pow _ _ ▸ Nat.div_eq_of_lt ( by exact lt_of_lt_of_le ( by decide ) ( Nat.pow_le_pow_right ( by decide ) hk ) );
    exact h_shift.symm ▸ rfl

-- test3
lemma test3_precondition :
  precondition test3_binary := by
  -- The string "10" consists of the characters '1' and '0', both of which are valid binary digits.
  simp [precondition, test3_binary];
  exact fun c hc => by rw [ String.toList ] at hc; aesop;

lemma test3_postcondition :
  postcondition test3_binary test3_Expected := by
  -- Let's verify the postcondition for test3, which is the binary string "10" and the decimal value 2.
  apply And.intro;
  · -- Let's verify the postcondition for test3.
    unfold ensures1 test3_binary test3_Expected;
    native_decide +revert;
  · -- For any k ≥ 2, the k-th bit of 2 is false because 2 in binary is 10.
    intro k hk
    simp [test3_Expected, Nat.testBit];
    rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.shiftRight_eq_div_pow ];
    norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]

-- test13
lemma test13_precondition :
  precondition test13_binary := by
  intro c hc; aesop;
  native_decide +revert

lemma test13_postcondition :
  postcondition test13_binary test13_Expected := by
  constructor;
  · -- By definition of `test13_binary` and `test13_Expected`, we need to show that the k-th bit of 42 is equal to the k-th bit of "101010".
    unfold ensures1 test13_binary test13_Expected;
    native_decide +revert;
  · -- For k ≥ 6, the binary string "101010" has no more bits, so all higher bits are 0.
    intro k hk
    simp [test13_binary, test13_Expected] at *;
    rcases k with ( _ | _ | _ | _ | _ | _ | _ | k ) <;> simp_all +arith +decide [ Nat.testBit ];
    norm_num [ Nat.shiftRight_eq_div_pow ];
    norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]

-- test18
lemma test18_precondition :
  precondition test18_binary := by
  exact fun c hc => by fin_cases hc <;> trivial;

lemma test18_postcondition :
  postcondition test18_binary test18_Expected := by
  -- We need to show that the decimal value of the binary string "1111111111" is 1023 and that the postcondition holds.
  apply And.intro;
  · -- We'll use the fact that `test18_binary` is "1111111111" and `test18_Expected` is 1023.
    have h_binary : test18_binary = "1111111111" := by
      rfl
    have h_decimal : test18_Expected = 1023 := by
      rfl;
    unfold ensures1; simp +decide [ h_binary, h_decimal ] ;
  · intro k hk
    simp [test18_binary, test18_Expected] at hk ⊢;
    rcases k with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> simp_all +decide [ Nat.testBit ];
    norm_num [ Nat.shiftRight_eq_div_pow ];
    rw [ Nat.div_eq_of_lt ] ; norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ];
    linarith [ Nat.one_le_pow k 2 ( by decide ) ]

-- test19
lemma test19_precondition :
  precondition test19_binary := by
  -- Check each character in the string "10000000000" to ensure they are either '0' or '1'.
  simp [precondition, test19_binary];
  -- Check each character in the string "10000000000" to ensure they are either '0' or '1'. We can do this by examining each character individually.
  intro c hc
  aesop

lemma test19_postcondition :
  postcondition test19_binary test19_Expected := by
  -- By definition of `postcondition`, we need to show that for all `k`, the `k`-th bit of `test19_Expected` matches the `k`-th bit of `test19_binary`. We can verify this by checking each bit.
  apply And.intro;
  · -- Let's verify the first part of the postcondition for test19. We need to show that for all k < 11, the k-th bit of 1024 is equal to the k-th bit of "10000000000".
    simp [ensures1, test19_binary, test19_Expected];
    native_decide;
  · -- We need to show that for all $k \geq 11$, the $k$-th bit of $1024$ is false.
    intro k hk
    simp [test19_binary, test19_Expected] at hk ⊢;
    rcases k with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> simp_all +arith +decide [ Nat.testBit ];
    norm_num [ Nat.shiftRight_eq_div_pow ];
    rw [ Nat.div_eq_of_lt ( by linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( by linarith : k + 12 ≥ 12 ) ] ), Nat.zero_mod ]

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (binary: String):
  precondition binary →
  (∀ ret1 ret2,
    postcondition binary ret1 →
    postcondition binary ret2 →
    ret1 = ret2) := by
  intros h_precondition ret1 ret2 hret1 hret2; exact (by
  refine' Nat.eq_of_testBit_eq fun k => _;
  by_cases hk : k < binary.length;
  · rw [ hret1.1 k hk, hret2.1 k hk ];
  · rw [ hret1.2 k ( le_of_not_gt hk ), hret2.2 k ( le_of_not_gt hk ) ])
