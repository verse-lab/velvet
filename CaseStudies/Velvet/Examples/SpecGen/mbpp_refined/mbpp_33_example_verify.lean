import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000

-- Helper Functions

def binaryToDecimal (bits: List Nat) : Nat :=
  bits.foldl (fun acc bit => 2 * acc + bit) 0

def allBinaryDigits (bits: List Nat) : Prop :=
  ∀ b ∈ bits, b = 0 ∨ b = 1

def noLeadingZeros (bits: List Nat) : Prop :=
  bits = [0] ∨ (bits.length > 0 ∧ bits.head? = some 1)

def ensures1 (n : Nat) (binary : List Nat) :=
  allBinaryDigits binary  -- All elements are 0 or 1
def ensures2 (n : Nat) (binary : List Nat) :=
  binaryToDecimal binary = n  -- The binary representation equals the decimal input
def ensures3 (n : Nat) (binary : List Nat) :=
  noLeadingZeros binary  -- No leading zeros (except for n=0)
def ensures4 (n : Nat) (binary : List Nat) :=
  binary.length > 0  -- Result is never empty

def precondition (n: Nat) :=
  True

def postcondition (n: Nat) (binary: List Nat) :=
  ensures1 n binary ∧ ensures2 n binary ∧ ensures3 n binary ∧ ensures4 n binary

-- Test Cases
def test1_n : Nat := 0

def test1_Expected : List Nat := [0]

def test2_n : Nat := 1

def test2_Expected : List Nat := [1]

def test3_n : Nat := 2

def test3_Expected : List Nat := [1, 0]

def test9_n : Nat := 10

def test9_Expected : List Nat := [1, 0, 1, 0]

def test17_n : Nat := 1000

def test17_Expected : List Nat := [1, 1, 1, 1, 1, 0, 1, 0, 0, 0]

def test20_n : Nat := 65535

def test20_Expected : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

-------------------------------
-- Verifications
-------------------------------

-- test1
lemma test1_precondition :
  precondition test1_n := by
  -- The precondition for `test1_n` is trivially true.
  simp [precondition]

lemma test1_postcondition :
  postcondition test1_n test1_Expected := by
  -- Let's verify each of the ensures conditions for the test case where n is 0 and the expected binary representation is [0].
  simp [postcondition, ensures1, ensures2, ensures3, ensures4];
  -- Let's verify each of the properties for the case when n is 0.
  simp [allBinaryDigits, binaryToDecimal, noLeadingZeros, test1_n, test1_Expected]

-- test2
lemma test2_precondition :
  precondition test2_n := by
  -- The precondition is trivially true for any natural number.
  apply trivial

lemma test2_postcondition :
  postcondition test2_n test2_Expected := by
  -- Let's verify the postcondition for the test case where n is 1 and the expected binary is [1].
  simp [postcondition, ensures1, ensures2, ensures3, ensures4];
  -- Let's verify the properties for the binary representation of 1.
  simp [allBinaryDigits, binaryToDecimal, noLeadingZeros];
  native_decide +revert

-- test3
lemma test3_precondition :
  precondition test3_n := by
  exact?

lemma test3_postcondition :
  postcondition test3_n test3_Expected := by
  -- Let's verify the postcondition for test3.
  constructor;
  · -- The list [1, 0] consists of valid binary digits (0 and 1).
    simp [ensures1];
    -- The list [1, 0] consists of valid binary digits (0 and 1), so we can conclude that allBinaryDigits holds.
    simp [allBinaryDigits, test3_Expected];
  · aesop;
    · exact Or.inr ⟨ by decide, rfl ⟩;
    · -- The length of the binary representation of 2 is 2, which is greater than 0.
      simp [ensures4, test3_Expected]

-- test9
lemma test9_precondition :
  precondition test9_n := by
  trivial

lemma test9_postcondition :
  postcondition test9_n test9_Expected := by
  -- Let's verify the postcondition for the test case 10.
  simp [postcondition, ensures1, ensures2, ensures3, ensures4];
  -- Let's verify the binary representation of 10.
  simp [test9_Expected, allBinaryDigits, binaryToDecimal, noLeadingZeros];
  bound

-- test17
lemma test17_precondition :
  precondition test17_n := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test17_postcondition :
  postcondition test17_n test17_Expected := by
  -- Let's verify each condition for the postcondition.
  constructor;
  · intro b hb; fin_cases hb <;> trivial;
  · aesop;
    · -- The list [1, 1, 1, 1, 1, 0, 1, 0, 0, 0] has no leading zeros and its length is greater than 0.
      simp [ensures3, noLeadingZeros];
      decide;
    · -- Let's verify the postcondition for test17_n. We need to show that the length of the binary representation is greater than 0.
      simp [ensures4];
      decide +revert

-- test20
lemma test20_precondition :
  precondition test20_n := by
  trivial

lemma test20_postcondition :
  postcondition test20_n test20_Expected := by
  -- Let's verify the postcondition for the test case with n = 65535.
  simp [postcondition, test20_n, test20_Expected];
  -- Let's verify the binary representation of 65535.
  simp [ensures1, ensures2, ensures3, ensures4];
  -- Let's verify that the binary representation of 65535 is correct.
  simp [allBinaryDigits, binaryToDecimal, noLeadingZeros]

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (n: Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  -- By definition of postcondition, if two lists of binary digits are both valid and represent the same number, then they must be the same list.
  intros h_precondition ret1 ret2 h_ret1 h_ret2
  have h_unique : binaryToDecimal ret1 = binaryToDecimal ret2 := by
    unfold postcondition at *; aesop;
    exact left_2.trans left_3.symm;
  -- We'll use induction on the length of the lists to prove that their binary representations are equal.
  have h_ind : ∀ (l1 l2 : List ℕ), (∀ b ∈ l1, b = 0 ∨ b = 1) → (∀ b ∈ l2, b = 0 ∨ b = 1) → List.length l1 = List.length l2 → binaryToDecimal l1 = binaryToDecimal l2 → l1 = l2 := by
    intros l1 l2 hl1 hl2 hlen h_eq; induction' l1 with d1 l1 ih generalizing l2 <;> induction' l2 with d2 l2 ih' <;> simp_all +arith +decide;
    unfold binaryToDecimal at h_eq; aesop;
    · exact ih l2 right_1 rfl h_eq;
    · -- By definition of `foldl`, we can expand both sides of the equation.
      have h_expand : ∀ (l : List ℕ), (∀ b ∈ l, b = 0 ∨ b = 1) → List.foldl (fun (acc bit : ℕ) => 2 * acc + bit) 0 l < 2 ^ l.length ∧ List.foldl (fun (acc bit : ℕ) => 2 * acc + bit) 1 l ≥ 2 ^ l.length := by
        intro l hl; induction' l using List.reverseRecOn with d l ih <;> aesop;
        · cases hl l ( Or.inr rfl ) <;> simp_all +decide [ pow_succ' ] ; linarith;
        · cases hl l ( Or.inr rfl ) <;> simp_all +decide [ pow_succ' ] ; linarith;
      grind +ring;
    · -- By definition of `List.foldl`, we can expand both sides of the equation.
      have h_foldl_expand : ∀ (l : List ℕ), (∀ b ∈ l, b = 0 ∨ b = 1) → List.foldl (fun (acc bit : ℕ) => 2 * acc + bit) 1 l ≥ 2 ^ l.length := by
        intro l hl; induction' l using List.reverseRecOn with d l ih <;> aesop;
        rw [ pow_succ' ] ; linarith [ show l ≥ 0 by positivity ];
      have h_foldl_expand' : ∀ (l : List ℕ), (∀ b ∈ l, b = 0 ∨ b = 1) → List.foldl (fun (acc bit : ℕ) => 2 * acc + bit) 0 l < 2 ^ l.length := by
        intro l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
        cases hl ih ( Or.inr rfl ) <;> simp_all +decide [ pow_succ' ] ; linarith;
      linarith [ h_foldl_expand l1 right, h_foldl_expand' l2 right_1, pow_pos ( zero_lt_two' ℕ ) l2.length, pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( by linarith : l1.length ≥ l2.length ) ];
    · specialize ih l2 ; aesop;
      apply ih;
      have h_eq_fold : ∀ (l : List ℕ), (∀ b ∈ l, b = 0 ∨ b = 1) → List.foldl (fun (acc bit : ℕ) => 2 * acc + bit) 1 l = 2 ^ l.length + List.foldl (fun (acc bit : ℕ) => 2 * acc + bit) 0 l := by
        intro l hl; induction' l using List.reverseRecOn with d l ih <;> aesop;
        ring;
      unfold binaryToDecimal; aesop;
  -- Since both ret1 and ret2 are valid binary representations of n, their lengths must be equal.
  have h_len : ret1.length = ret2.length := by
    -- By definition of binary representation, the length of the binary representation of n is equal to the number of digits in the binary representation of n.
    have h_len : ∀ (l : List ℕ), (∀ b ∈ l, b = 0 ∨ b = 1) → binaryToDecimal l < 2 ^ l.length := by
      intro l hl; induction' l using List.reverseRecOn with d _ ih <;> aesop;
      unfold binaryToDecimal at *;
      cases hl a ( Or.inr rfl ) <;> simp_all +decide [ pow_succ' ] ; linarith;
    -- If ret1.length < ret2.length, then 2^ret1.length ≤ n < 2^ret2.length, which contradicts n = binaryToDecimal ret1.
    by_cases h_len_lt : ret1.length < ret2.length;
    · have h_contradiction : binaryToDecimal ret2 ≥ 2 ^ ret1.length := by
        -- Since ret2 is a valid binary representation, its first element must be 1.
        have h_first_one : ret2.head? = some 1 := by
          cases h_ret2.2.2.1 <;> aesop;
          cases h_ret1.2.2.2;
        rcases ret2 <;> aesop;
        -- By definition of binaryToDecimal, we can expand the expression for binaryToDecimal (1 :: tail).
        have h_expand : binaryToDecimal (1 :: tail) = 2 ^ tail.length + binaryToDecimal tail := by
          unfold binaryToDecimal; induction tail using List.reverseRecOn <;> aesop;
          clear h_unique h_len_lt h_ind h_len a_1 h_ret2 h_ret1 h_precondition;
          induction l using List.reverseRecOn <;> aesop;
          norm_num [ pow_succ' ] at * ; linarith;
        exact h_expand.symm ▸ le_add_of_le_of_nonneg ( pow_le_pow_right₀ ( by decide ) ( by linarith ) ) ( Nat.zero_le _ );
      linarith [ h_len ret1 h_ret1.1 ];
    · by_cases h_len_gt : ret1.length > ret2.length;
      · have h_contradiction : 2 ^ ret2.length ≤ binaryToDecimal ret1 := by
          have h_contradiction : ∀ (l : List ℕ), (∀ b ∈ l, b = 0 ∨ b = 1) → l.length > 0 → l.head? = some 1 → 2 ^ (l.length - 1) ≤ binaryToDecimal l := by
            intros l hl hl_pos hl_head
            induction' l with d l ih;
            · contradiction;
            · -- Since $d$ is either $0$ or $1$, we can split into cases.
              cases' hl d (by simp) with hd hd;
              · cases l <;> aesop;
              · unfold binaryToDecimal; simp +arith +decide [ hd ] ;
                -- By induction on the length of the list l, we can show that the foldl result is at least 2^l.length.
                have h_ind : ∀ (l : List ℕ), (∀ b ∈ l, b = 0 ∨ b = 1) → List.foldl (fun (acc bit : ℕ) => 2 * acc + bit) 1 l ≥ 2 ^ l.length := by
                  intro l hl; induction' l using List.reverseRecOn with d l ih <;> norm_num [ Nat.pow_succ' ] at *;
                  exact le_add_of_le_of_nonneg ( Nat.mul_le_mul_left _ ( ih fun b hb => hl b ( Or.inl hb ) ) ) ( Nat.zero_le _ );
                exact h_ind l fun b hb => hl b <| List.mem_cons_of_mem _ hb;
          refine le_trans ?_ ( h_contradiction ret1 h_ret1.1 ( by linarith ) ?_ );
          · exact pow_le_pow_right₀ ( by decide ) ( Nat.le_pred_of_lt h_len_gt );
          · cases h_ret1.2.2.1 <;> aesop;
            cases h_ret2.2.2.2;
        linarith [ h_len ret2 h_ret2.1 ];
      · linarith;
  exact h_ind ret1 ret2 h_ret1.1 h_ret2.1 h_len h_unique
