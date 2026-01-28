import Lean
import Mathlib.Tactic


-- Helper Functions

def ensures1 (s : List Char) (count : Nat) :=
  count = Nat.card
    { p : Nat × Nat |
        let i := p.1
        let j := p.2
        i ≤ j ∧
        j < s.length ∧
        s[i]! = s[j]! }

def precondition (s: List Char) :=
  True

def postcondition (s: List Char) (count: Nat) :=
  ensures1 s count

-- Test Cases
def test0_s : List Char := ['a', 'b', 'c']

def test0_Expected : Nat := 3

def test1_s : List Char := []

def test1_Expected : Nat := 0

def test2_s : List Char := ['a']

def test2_Expected : Nat := 1

def test3_s : List Char := ['a', 'a']

def test3_Expected : Nat := 3

def test4_s : List Char := ['a', 'a', 'a', 'a']

def test4_Expected : Nat := 10

-------------------------------
-- Verifications
-------------------------------

-- test0
lemma test0_precondition :
  precondition test0_s := by
  -- The precondition for `test0_s` is true by definition.
  simp [precondition]

lemma test0_postcondition :
  postcondition test0_s test0_Expected := by
  simp [postcondition, ensures1, test0_Expected, test0_s]
  -- Let's explicitly calculate the set {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.2 < 3 ∧ ['a', 'b', 'c'][p.1]?.getD 'A' = ['a', 'b', 'c'][p.2]?.getD 'A'}.
  have h_set : {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.2 < 3 ∧ ['a', 'b', 'c'][p.1]?.getD 'A' = ['a', 'b', 'c'][p.2]?.getD 'A'} = {(0, 0), (1, 1), (2, 2)} := by
    -- Let's explicitly list out the pairs in the set for n = 3 and verify they match the expected result.
    ext ⟨i, j⟩
    rcases i with ( _ | _ | _ | i ) <;> rcases j with ( _ | _ | _ | j ) <;> simp_all +arith +decide;
  rw [ show { p : ℕ × ℕ // p.1 ≤ p.2 ∧ p.2 < 3 ∧ _ } = { p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.2 < 3 ∧ _ } from rfl, h_set ] ; simp +decide

-- test1
lemma test1_precondition :
  precondition test1_s := by
  -- The precondition for the empty string is trivially true.
  simp [precondition]

lemma test1_postcondition :
  postcondition test1_s test1_Expected := by
  -- In the case where the string is empty, there are no pairs to consider, so the count is 0.
  simp [postcondition, test1_s, test1_Expected];
  -- The base case is when the list is empty. In this case, there are no pairs, so the count is 0.
  simp [ensures1]

-- test2
lemma test2_precondition :
  precondition test2_s := by
  exact?

lemma test2_postcondition :
  postcondition test2_s test2_Expected := by
  -- Let's simplify the goal.
  unfold postcondition;
  -- The only pair (i, j) that satisfies i ≤ j is (0, 0), and since the string has only one element, the count is 1.
  simp [ensures1, test2_s, test2_Expected];
  -- Let's simplify the set {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.2 = 0 ∧ ['a'][p.1]?.getD 'A' = ['a'][p.2]?.getD 'A'}.
  have h_set : {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.2 = 0 ∧ ['a'][p.1]?.getD 'A' = ['a'][p.2]?.getD 'A'} = {(0, 0)} := by
    ext ⟨ x, y ⟩ ; aesop;
  -- The cardinality of the set {(0, 0)} is 1.
  have h_card : Nat.card {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.2 = 0 ∧ ['a'][p.1]?.getD 'A' = ['a'][p.2]?.getD 'A'} = 1 := by
    exact h_set ▸ by norm_num;
  exact h_card.symm

-- test3
lemma test3_precondition :
  precondition test3_s := by
  exact?

lemma test3_postcondition :
  postcondition test3_s test3_Expected := by
  -- We can calculate the set size directly.
  have h_card : Nat.card {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.2 < 2 ∧ (test3_s[p.1]! = test3_s[p.2]!)} = 3 := by
    -- List all pairs (i, j) where i ≤ j and j < 2.
    have h_pairs : {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.2 < 2 ∧ (test3_s[p.1]! = test3_s[p.2]!)} = {(0, 0), (0, 1), (1, 1)} := by
      ext ⟨i, j⟩;
      rcases i with ( _ | _ | i ) <;> rcases j with ( _ | _ | j ) <;> simp +arith +decide;
    simp +decide only [h_pairs, Nat.card_eq_fintype_card];
  exact?

-- test4
lemma test4_precondition :
  precondition test4_s := by
  exact?

lemma test4_postcondition :
  postcondition test4_s test4_Expected := by
  -- Let's calculate the set of pairs (i, j) where i ≤ j, j < 4, and the elements at these indices are equal.
  have h_pairs : {p : Nat × Nat | p.1 ≤ p.2 ∧ p.2 < 4 ∧ test4_s[p.1]! = test4_s[p.2]!} = {(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)} := by
    -- Let's list out all pairs (i, j) where i ≤ j and j < 4.
    ext ⟨i, j⟩
    simp [test4_s];
    -- Let's consider all possible pairs (i, j) where i ≤ j and j < 4.
    by_cases hj : j < 4;
    · interval_cases j <;> rcases i with ( _ | _ | _ | _ | i ) <;> simp_all +decide;
    · grind;
  -- Therefore, the cardinality of the set is 10.
  have h_card : Nat.card {p : Nat × Nat | p.1 ≤ p.2 ∧ p.2 < 4 ∧ test4_s[p.1]! = test4_s[p.2]!} = 10 := by
    simp +decide only [h_pairs, Nat.card_eq_fintype_card];
  -- Apply the definition of postcondition and use h_card to conclude the proof.
  apply Eq.symm; exact (by
    exact h_card
  )

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (s: List Char):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  -- By definition of postcondition, if ret1 and ret2 both satisfy the postcondition, then they must be equal to countMatchingSubstrings s.
  intro h_pre ret1 ret2 h1 h2
  rw [h1, h2]
