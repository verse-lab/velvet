import Lean
import Mathlib.Tactic

-- Helper Functions

def isDigit (c : Char) : Bool := c.isDigit

-- Helper function to remove all digits from a single string
def isRemoveDigits (s : String) (t : String) :=
  t = String.mk (s.data.filter (fun c => !isDigit c))

-- Postcondition clauses
def ensures1 (strings : List String) (result : List String) :=
  result.length = strings.length ∧
  ∀ i, i < strings.length → isRemoveDigits strings[i]! result[i]!

def precondition (strings: List String) :=
  True

def postcondition (strings: List String) (result: List String) :=
  ensures1 strings result

-- Test Cases
def test0_arr : List String := ["4words", "3letters", "4digits"]

def test0_Expected : List String := ["words", "letters", "digits"]

def test2_arr : List String := ["123", "456", "789"]

def test2_Expected : List String := ["", "", ""]

def test3_arr : List String := ["a1b2c3", "x9y8z7", "m5n6"]

def test3_Expected : List String := ["abc", "xyz", "mn"]

def test4_arr : List String := []

def test4_Expected : List String := []

def test7_arr : List String := ["hello123!", "test@456#", "code789$"]

def test7_Expected : List String := ["hello!", "test@#", "code$"]

def test10_arr : List String := [
  "abc123", "def456", "ghi789", "jkl012", "mno345",
  "pqr678", "stu901", "vwx234", "yza567", "bcd890",
  "efg123", "hij456", "klm789", "nop012", "qrs345",
  "tuv678", "wxy901", "zab234", "cde567", "fgh890"
]

def test10_Expected : List String := [
  "abc", "def", "ghi", "jkl", "mno",
  "pqr", "stu", "vwx", "yza", "bcd",
  "efg", "hij", "klm", "nop", "qrs",
  "tuv", "wxy", "zab", "cde", "fgh"
]

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test0
----------------------------
lemma test0_precondition :
  precondition test0_arr := by
  trivial

lemma test0_postcondition :
  postcondition test0_arr test0_Expected := by
  simp [postcondition, test0_arr, test0_Expected, ensures1, isRemoveDigits];
  intros i hi
  interval_cases i <;> trivial

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_arr := by
  trivial

lemma test2_postcondition :
  postcondition test2_arr test2_Expected := by
  simp [postcondition, test2_arr, test2_Expected, ensures1, isRemoveDigits];
  intros i hi
  interval_cases i <;> trivial


----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_arr := by
  exact?

lemma test3_postcondition :
  postcondition test3_arr test3_Expected := by
  simp [postcondition, test3_arr, test3_Expected, ensures1, isRemoveDigits];
  intros i hi
  interval_cases i <;> trivial

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_arr := by
  trivial

lemma test4_postcondition :
  postcondition test4_arr test4_Expected := by
  -- The empty list satisfies all conditions trivially.
  simp [postcondition, test4_arr, test4_Expected, ensures1, isRemoveDigits]

----------------------------
-- Verification: test7
----------------------------
lemma test7_precondition :
  precondition test7_arr := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test7_postcondition :
  postcondition test7_arr test7_Expected := by
  simp [postcondition, test7_arr, test7_Expected, ensures1, isRemoveDigits];
  intros i hi
  interval_cases i <;> trivial

----------------------------
-- Verification: test10
----------------------------
lemma test10_precondition :
  precondition test10_arr := by
  exact?

lemma test10_postcondition :
  postcondition test10_arr test10_Expected := by
  simp [postcondition, test10_arr, test10_Expected, ensures1, isRemoveDigits];
  intros i hi
  interval_cases i <;> trivial

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (strings: List String):
  precondition strings →
  (∀ ret1 ret2,
    postcondition strings ret1 →
    postcondition strings ret2 →
    ret1 = ret2) := by
  unfold precondition postcondition;
  unfold ensures1;
  unfold isRemoveDigits;
  norm_num +zetaDelta at *;
  intro ret1 ret2 h1 h2 h3 h4; ext i; by_cases hi : i < strings.length <;> aesop;
