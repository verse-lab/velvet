import Lean
import Mathlib.Tactic

-- Helper Functions

def startsWithWord (s: String) : Bool :=
  match s.data with
  | [] => false
  | c :: _ => c.isAlpha
-- The expected result based on whether the string starts with a word

def expectedResult (s: String) : String :=
  if startsWithWord s then "Matched!" else "Not matched!"

def ensures1 (input : String) (result : String) :=
  result = "Matched!" ∨ result = "Not matched!"
def ensures2 (input : String) (result : String) :=
  result = "Matched!" ↔ startsWithWord input

def precondition (input: String) :=
  True

def postcondition (input: String) (result: String) :=
  ensures1 input result ∧ ensures2 input result

-- Test Cases
def test1_input : String := " python"

def test1_Expected : String := "Not matched!"

def test2_input : String := "python"

def test2_Expected : String := "Matched!"

def test3_input : String := ""

def test3_Expected : String := "Not matched!"

def test4_input : String := "123abc"

def test4_Expected : String := "Not matched!"

def test5_input : String := "!hello"

def test5_Expected : String := "Not matched!"

def test6_input : String := "a"

def test6_Expected : String := "Matched!"

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_input := by
  exact?

lemma test1_postcondition :
  postcondition test1_input test1_Expected := by
  -- Let's verify the postcondition for the test case where the input is " python".
  simp [postcondition, test1_Expected];
  -- Let's verify each part of the conjunction separately.
  simp [ensures1, ensures2];
  bound

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_input := by
  exact?

lemma test2_postcondition :
  postcondition test2_input test2_Expected := by
  -- By definition of `postcondition`, we need to show that the result is either "Matched!" or "Not matched!".
  unfold postcondition;
  -- By definition of `postcondition`, we need to show that the result is either "Matched!" or "Not matched!" and that the result is "Matched!" if and only if the string starts with a word.
  simp [ensures1, ensures2];
  decide +revert

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_input := by
  exact?

lemma test3_postcondition :
  postcondition test3_input test3_Expected := by
  -- Since the input is empty, the result is "Not matched!", which satisfies the first part of the postcondition.
  simp [postcondition, test3_Expected];
  -- Since the input is empty, the result is "Not matched!", which satisfies all three parts of the postcondition.
  simp [ensures1, ensures2, test3_input];
  -- Since the input is empty, the result is "Not matched!", which satisfies all three parts of the postcondition. We can verify this by checking each part individually.
  simp [startsWithWord]

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_input := by
  exact?

lemma test4_postcondition :
  postcondition test4_input test4_Expected := by
  -- Check that the postcondition holds for test4_input and test4_Expected.
  simp [postcondition, ensures1, ensures2];
  decide +kernel

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_input := by
  exact?

lemma test5_postcondition :
  postcondition test5_input test5_Expected := by
  -- Since the first character of "!hello" is '!', which is not alphabetic, the expected result is "Not matched!".
  have h_test5 : expectedResult "!hello" = "Not matched!" := by
    decide +revert;
  -- By combining the results from h_test5 and the fact that beginsWithWord returns false for "!hello", we can conclude that the postcondition holds for test5.
  simp [postcondition];
  -- Since the first character of "!hello" is '!', which is not alphabetic, the expected result is "Not matched!" and the postcondition holds.
  simp [ensures1, ensures2, test5_input, test5_Expected];
  native_decide +revert

----------------------------
-- Verification: test6
----------------------------
lemma test6_precondition :
  precondition test6_input := by
  exact?

lemma test6_postcondition :
  postcondition test6_input test6_Expected := by
  -- By definition of `postcondition`, we need to show that `test6_Expected = "Matched!"` if and only if `startsWithWord test6_input`.
  simp [postcondition, test6_Expected, test6_input];
  -- Let's unfold the definitions of ensures1, ensures2, and ensures3.
  unfold ensures1 ensures2;
  -- Let's simplify the goal.
  simp (config := { decide := true }) only

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (input: String):
  precondition input →
  (∀ ret1 ret2,
    postcondition input ret1 →
    postcondition input ret2 →
    ret1 = ret2) := by
  -- By definition of postcondition, if both ret1 and ret2 satisfy the postcondition, then they must both be equal to the expected result.
  intros h_pre ret1 ret2 h1 h2
  simp [postcondition, ensures1, ensures2] at *
  obtain ⟨ h1a, h1b ⟩ := h1
  obtain ⟨ h2a, h2b ⟩ := h2
  cases h1a <;> cases h2a <;> aesop
