import Lean
import Mathlib.Tactic

-- Helper Functions

def containsPattern (input : List Char) : Prop :=
  ∃ i j k,
    0 ≤ i ∧ i < j ∧ j < k ∧ k < input.length ∧
    (∀ p, i ≤ p → p < j → input[p]!.isLower) ∧
    input[j]! = '_' ∧
    (∀ p, j < p → p ≤ k → input[p]!.isLower)

-- Postcondition clauses
def ensures1 (input : List Char) (result : String) :=
  containsPattern input → result = "Found a match!"
def ensures2 (input : List Char) (result : String) :=
  ¬containsPattern input → result = "Not matched!"

def precondition (input: List Char) :=
  True

def postcondition (input: List Char) (result: String) :=
  ensures1 input result ∧ ensures2 input result

-- Test Cases
def test0_input : List Char := ['a','a','b','_','c','b','b','b','c']
def test0_Expected : String := "Found a match!"

-- Test case 1: Simple valid pattern
def test1_input : List Char := ['h','e','l','l','o','_','w','o','r','l','d']
def test1_Expected : String := "Found a match!"

-- Test case 2: No underscore
def test2_input : List Char := ['h','e','l','l','o','w','o','r','l','d']
def test2_Expected : String := "Not matched!"

-- Test case 3: Underscore at start
def test3_input : List Char := ['_','t','e','s','t']
def test3_Expected : String := "Not matched!"

-- Test case 4: Underscore at end
def test4_input : List Char := ['t','e','s','t','_']
def test4_Expected : String := "Not matched!"

-- Test case 5: Double underscore
def test5_input : List Char := ['t','e','s','t','_','_','c','a','s','e']
def test5_Expected : String := "Not matched!"

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test0
----------------------------
lemma test0_precondition :
  precondition test1_input := by
  exact?

lemma test0_postcondition :
  postcondition test0_input test0_Expected := by
  -- Show that the test0_input satisfies the postcondition.
  simp [postcondition, test0_input, test0_Expected];
  -- Show that the test0_input satisfies the postcondition by verifying the conditions for ensures1 and ensures2.
  simp [ensures1, ensures2] at *;
  -- Let's choose the indices $i = 0$, $j = 3$, and $k = 8$.
  use 0, 3, 8;
  simp +arith +decide

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_input := by
  exact?

lemma test1_postcondition :
  postcondition test1_input test1_Expected := by
  constructor;
  · -- Apply the ensures1 lemma to the specific input and expected result.
    apply fun h => rfl;
  · -- Since there is a valid pattern in the input, the result should be "Found a match!".
    simp [ensures2, test1_Expected];
    -- For the input "hello_world", we can choose $i = 0$, $j = 5$, and $k = 10$.
    use 0, 5, 10;
    simp +arith +decide

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_input := by
  exact?

lemma test2_postcondition :
  postcondition test2_input test2_Expected := by
  unfold postcondition;
  unfold ensures1 ensures2 test2_input test2_Expected;
  -- Since there are no underscores in the input, the pattern cannot be found.
  simp [containsPattern];
  intro x y hxy z hxy' hz h h'; interval_cases z <;> interval_cases y <;> interval_cases x <;> simp +decide at h h' ⊢;

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_input := by
  exact?

lemma test3_postcondition :
  postcondition test3_input test3_Expected := by
  constructor;
  · intro h;
    obtain ⟨ i, j, k, hij, hjk, hk, h₁, h₂, h₃ ⟩ := h;
    rcases j with ( _ | _ | j ) <;> rcases k with ( _ | _ | k ) <;> simp_all +decide [ test3_input ];
    grind;
  · -- By definition of ensures2, we need to show that if there's no match in the input, the result is "Not matched!".
    unfold ensures2;
    aesop

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_input := by
  exact?

lemma test4_postcondition :
  postcondition test4_input test4_Expected := by
  constructor;
  · rintro ⟨ i, j, k, hi, hj, hk, hlt, h₁, h₂, h₃ ⟩ ; rcases i with ( _ | _ | _ | _ | _ | i ) <;> rcases j with ( _ | _ | _ | _ | _ | j ) <;> rcases k with ( _ | _ | _ | _ | _ | k ) <;> trivial;
  · exact?

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_input := by
  exact?

lemma test5_postcondition :
  postcondition test5_input test5_Expected := by
  -- By definition of `test5_Expected`, we know that it is equal to "Not matched!".
  simp [postcondition, test5_Expected];
  -- Since the input list does not contain the pattern, the result should be "Not matched!".
  simp [ensures1, ensures2, test5_input];
  -- To prove the negation, we show that there are no indices i, j, k such that the conditions hold.
  intro h
  obtain ⟨i, j, k, hi, hj, hk, h_len, h_lower1, h_underscore, h_lower2⟩ := h;
  -- Since j must be 4 or 5, let's check the possible values of k.
  have h_j_values : j = 4 ∨ j = 5 := by
    rcases j with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j ) <;> simp_all +arith +decide;
  rcases h_j_values with ( rfl | rfl ) <;> simp_all +arith +decide;
  · interval_cases k <;> simp_all +decide;
  · interval_cases k <;> specialize h_lower1 4 <;> simp_all +decide

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (input: List Char):
  precondition input →
  (∀ ret1 ret2,
    postcondition input ret1 →
    postcondition input ret2 →
    ret1 = ret2) := by
  unfold postcondition; aesop;
  unfold ensures1 at *;
  by_cases h : containsPattern input <;> aesop;
  unfold ensures2 at *; aesop;
