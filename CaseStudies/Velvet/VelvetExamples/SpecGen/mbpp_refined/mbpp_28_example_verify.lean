import Lean
import Mathlib.Tactic

-- Helper Functions

def binomialCoeff (n: Nat) (k: Nat) : Nat :=
  if k > n then 0
  else n.factorial / (k.factorial * (n - k).factorial)

def require1 (n : Nat) (k : Nat) :=
  k ≤ n  -- k cannot exceed n

-- Postcondition clauses

def ensures1 (n : Nat) (k : Nat) (result : Nat) :=
  result = binomialCoeff n k  -- The result equals the binomial coefficient

def precondition (n: Nat) (k: Nat) :=
  require1 n k

def postcondition (n: Nat) (k: Nat) (result: Nat) :=
  ensures1 n k result

-- Test Cases
def test0_n : Nat := 5

def test0_k : Nat := 2

def test0_Expected : Nat := 10

def test1_n : Nat := 10

def test1_k : Nat := 0

def test1_Expected : Nat := 1

def test2_n : Nat := 7

def test2_k : Nat := 7

def test2_Expected : Nat := 1

def test3_n : Nat := 8

def test3_k : Nat := 1

def test3_Expected : Nat := 8

def test9_n : Nat := 10

def test9_k : Nat := 5

def test9_Expected : Nat := 252

def test14_n : Nat := 20

def test14_k : Nat := 10

def test14_Expected : Nat := 184756

-------------------------------
-- Verifications
-------------------------------

-- test0
lemma test0_precondition :
  precondition test0_n test0_k := by
  -- Since $2 \leq 5$, the precondition holds.
  simp [precondition, test0_n, test0_k];
  -- We can verify that 2 ≤ 5 directly.
  apply le_of_lt; norm_num

lemma test0_postcondition :
  postcondition test0_n test0_k test0_Expected := by
  -- We need to show that the result is indeed the binomial coefficient for the given inputs.
  simp [postcondition, test0_n, test0_k, test0_Expected];
  -- Calculate the binomial coefficient C(5, 2) using the definition.
  have h_binom : binomialCoeff 5 2 = 10 := by
    native_decide +revert;
  -- By definition of `ensures1` and `ensures2`, we need to show that `10 = binomialCoeff 5 2` and `10 > 0`.
  simp [ensures1, h_binom]

-- test1
lemma test1_precondition :
  precondition test1_n test1_k := by
  -- The precondition is that $k \leq n$, which is true since $0 \leq 10$.
  exact Nat.zero_le 10

lemma test1_postcondition :
  postcondition test1_n test1_k test1_Expected := by
  rfl

-- test2
lemma test2_precondition :
  precondition test2_n test2_k := by
  -- Since $7 \leq 7$ is trivially true, we can use the reflexive property of ≤.
  exact le_refl 7

lemma test2_postcondition :
  postcondition test2_n test2_k test2_Expected := by
  rfl

-- test3
lemma test3_precondition :
  precondition test3_n test3_k := by
  -- By definition of `require1`, we need to show that `k ≤ n`.
  simp [precondition];
  simp +decide [ require1 ]

lemma test3_postcondition :
  postcondition test3_n test3_k test3_Expected := by
  -- For the test case where n=8 and k=1, we need to show that the result equals the binomial coefficient and is positive.
  rfl;

-- test9
lemma test9_precondition :
  precondition test9_n test9_k := by
  exact Nat.le_of_lt_succ ( by decide )

lemma test9_postcondition :
  postcondition test9_n test9_k test9_Expected := by
  rfl

-- test14
lemma test14_precondition :
  precondition test14_n test14_k := by
  -- We need to show that $10 \leq 20$.
  simp [precondition];
  -- We need to show that $10 \leq 20$, which is true by definition.
  simp [require1];
  decide +revert

lemma test14_postcondition :
  postcondition test14_n test14_k test14_Expected := by
  rfl

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (n: Nat) (k: Nat):
  precondition n k →
  (∀ ret1 ret2,
    postcondition n k ret1 →
    postcondition n k ret2 →
    ret1 = ret2) := by
  -- If both ret1 and ret2 satisfy the postcondition, then by definition, they must both equal the binomial coefficient. Hence, they are equal to each other.
  intros h_pre ret1 ret2 h_post1 h_post2
  have h_eq : ret1 = binomialCoeff n k ∧ ret2 = binomialCoeff n k := by
    -- By definition of postcondition, if h_post1 and h_post2 are true, then ret1 and ret2 are both equal to binomialCoeff n k.
    apply And.intro h_post1 h_post2;
  rw [ h_eq.1, h_eq.2 ]
