import Lean
import Mathlib.Tactic

-- Helper Functions

def inArray (arr: Array Int) (val: Int) : Prop :=
  ∃ i, i < arr.size ∧ arr[i]! = val

def isSorted (arr: Array Int) : Prop :=
  ∀ i j, i < j → j < arr.size → arr[i]! < arr[j]!

def adjacentDiffAtMostTwo (arr: Array Int) : Prop :=
  ∀ i, i + 1 < arr.size → arr[i + 1]! - arr[i]! ≤ 2

def adjacentDiffAtLeastOne (arr: Array Int) : Prop :=
  ∀ i, i + 1 < arr.size → arr[i + 1]! - arr[i]! ≥ 1

def hasExactlyOneGap (arr: Array Int) : Prop :=
  (∃ k, k + 1 < arr.size ∧ arr[k + 1]! - arr[k]! = 2) ∧
  (∀ i j, i + 1 < arr.size → j + 1 < arr.size →
    arr[i + 1]! - arr[i]! = 2 → arr[j + 1]! - arr[j]! = 2 → i = j)

def require1 (arr : Array Int) :=
  arr.size ≥ 2  -- Need at least 2 elements to determine the sequence
def require2 (arr : Array Int) :=
  isSorted arr  -- Array must be sorted
def require3 (arr : Array Int) :=
  adjacentDiffAtLeastOne arr  -- Elements are distinct (strictly increasing)
def require4 (arr : Array Int) :=
  adjacentDiffAtMostTwo arr  -- Adjacent elements differ by at most 2
def require5 (arr : Array Int) :=
  hasExactlyOneGap arr  -- Exactly one gap of size 2
  -- The missing number is not in the array

-- Postcondition clauses

def ensures1 (arr : Array Int) (missing : Int) :=
  ¬inArray arr missing
def ensures2 (arr : Array Int) (missing : Int) :=
  arr[0]! < missing ∧ missing < arr[arr.size - 1]!
def ensures3 (arr : Array Int) (missing : Int) :=
  ∃ k, k + 1 < arr.size ∧ arr[k + 1]! - arr[k]! = 2 ∧ missing = arr[k]! + 1

def precondition (arr: Array Int) :=
  require1 arr ∧ require2 arr ∧ require3 arr ∧ require4 arr ∧ require5 arr

def postcondition (arr: Array Int) (missing: Int) :=
  ensures1 arr missing ∧ ensures2 arr missing ∧ ensures3 arr missing

-- Test Cases
def test0_arr : Array Int := #[1, 2, 3, 5]

def test0_Expected : Int := 4

def test1_arr : Array Int := #[1, 2, 4, 5, 6]

def test1_Expected : Int := 3

def test2_arr : Array Int := #[0, 1, 3, 4, 5]

def test2_Expected : Int := 2

def test3_arr : Array Int := #[10, 11, 12, 13, 15]

def test3_Expected : Int := 14

def test4_arr : Array Int := #[-5, -3, -2, -1]

def test4_Expected : Int := -4

def test8_arr : Array Int := #[5, 7]

def test8_Expected : Int := 6

-------------------------------
-- Verifications
-------------------------------

-- test0
lemma test0_precondition :
  precondition test0_arr := by
  -- Check that the array [1, 2, 3, 5] satisfies the precondition.
  simp [precondition, require1, require2, require3, require4, require5];
  -- We verify that the array [1, 2, 3, 5] satisfies the conditions.
  simp [test0_arr, isSorted, adjacentDiffAtLeastOne, adjacentDiffAtMostTwo, hasExactlyOneGap];
  simp +arith +decide;
  exact ⟨ by intro i j hij hj; interval_cases j <;> interval_cases i <;> trivial, by intro i j hi hj h1 h2; interval_cases i <;> interval_cases j <;> trivial ⟩

lemma test0_postcondition :
  postcondition test0_arr test0_Expected := by
  unfold postcondition;
  -- Verify that the missing number 4 is not in the array.
  have h1 : ¬inArray test0_arr 4 := by
    rintro ⟨ i, hi, hi' ⟩ ; rcases i with ( _ | _ | _ | _ | i ) <;> trivial;
  unfold ensures1 ensures2 ensures3; aesop;
  · decide +revert;
  · decide;
  · exists 2;

-- test1
lemma test1_precondition :
  precondition test1_arr := by
  -- Check that the array [1, 2, 4, 5, 6] satisfies all the preconditions.
  constructor;
  · exact Nat.le_add_left _ _;
  · aesop;
    · intro i j hij;
      rcases i with ( _ | _ | _ | _ | _ | i ) <;> rcases j with ( _ | _ | _ | _ | _ | j ) <;> tauto;
    · exact fun i hi => by rcases i with ( _ | _ | _ | _ | _ | i ) <;> trivial;
    · exact fun i hi => by rcases i with ( _ | _ | _ | _ | _ | i ) <;> trivial;
    · -- Check that there is exactly one gap of size 2 in the array.
      simp [require5, test1_arr];
      -- Check that there is exactly one gap of size 2 in the array #[1, 2, 4, 5, 6].
      constructor;
      · exists 1;
      · rintro ( _ | _ | _ | _ | _ | i ) ( _ | _ | _ | _ | _ | j ) <;> simp +arith +decide

lemma test1_postcondition :
  postcondition test1_arr test1_Expected := by
  -- Let's verify the postcondition for the test case.
  constructor;
  · exact fun ⟨ i, hi, hi' ⟩ ↦ by rcases i with ( _ | _ | _ | _ | _ | i ) <;> trivial;
  · aesop;
    · exact ⟨ by decide, by decide ⟩;
    · exists 1;

-- test2
lemma test2_precondition :
  precondition test2_arr := by
  apply And.intro;
  · -- The array test2_arr has 5 elements, which is greater than or equal to 2.
    simp [require1, test2_arr];
  · unfold require2 require3 require4 require5 test2_arr;
    bound;
    · intro i j hij;
      rcases i with ( _ | _ | _ | _ | _ | i ) <;> rcases j with ( _ | _ | _ | _ | _ | j ) <;> tauto;
    · exact fun i hi => by rcases i with ( _ | _ | _ | _ | _ | i ) <;> trivial;
    · exact fun i hi => by rcases i with ( _ | _ | _ | _ | _ | i ) <;> trivial;
    · -- Show that there exists exactly one position where the difference between adjacent elements is 2.
      use ⟨1, by decide, by decide⟩;
      rintro ( _ | _ | _ | _ | _ | i ) ( _ | _ | _ | _ | _ | j ) <;> norm_num

lemma test2_postcondition :
  postcondition test2_arr test2_Expected := by
  constructor;
  · -- We need to show that 2 is not in the array [0, 1, 3, 4, 5].
    simp [ensures1, test2_arr];
    -- We need to show that 2 is not in the array [0, 1, 3, 4, 5]. We can do this by checking each element.
    simp [inArray, test2_Expected];
    native_decide;
  · bound;
    · -- The missing number 2 is between the minimum (0) and maximum (5) of the array.
      simp [ensures2, test2_arr, test2_Expected];
    · exists 1;

-- test3
lemma test3_precondition :
  precondition test3_arr := by
  -- Verify that the test3_arr satisfies the precondition.
  constructor;
  · exact Nat.le_add_left _ _;
  · unfold require2 require3 require4 require5;
    unfold isSorted adjacentDiffAtLeastOne adjacentDiffAtMostTwo hasExactlyOneGap; simp +decide ;
    unfold test3_arr;
    simp +arith +decide;
    exact ⟨ fun i j hij hj => by interval_cases j <;> interval_cases i <;> trivial, fun i j hi hj h₁ h₂ => by interval_cases i <;> interval_cases j <;> trivial ⟩

lemma test3_postcondition :
  postcondition test3_arr test3_Expected := by
  -- Let's verify the postcondition for the test case `test3`.
  apply And.intro;
  · exact fun h => by obtain ⟨ i, hi, hi' ⟩ := h; rcases i with ( _ | _ | _ | _ | _ | i ) <;> trivial;
  · bound;
    · exact ⟨ by decide, by decide ⟩;
    · -- Let's choose k = 3, which satisfies the conditions.
      use 3;
      native_decide;

-- test4
lemma test4_precondition :
  precondition test4_arr := by
  constructor;
  · exact Nat.le_add_left _ _;
  · refine' ⟨ _, _, _, _ ⟩;
    · intro i j hij hj;
      rcases i with ( _ | _ | _ | _ | i ) <;> rcases j with ( _ | _ | _ | _ | _ | j ) <;> norm_cast;
    · exact fun i hi => by rcases i with ( _ | _ | _ | _ | i ) <;> trivial;
    · exact fun i hi => by rcases i with ( _ | _ | _ | _ | i ) <;> trivial;
    · constructor;
      · exists 0;
      · rintro ( _ | _ | _ | i ) ( _ | _ | _ | j ) <;> tauto

lemma test4_postcondition :
  postcondition test4_arr test4_Expected := by
  -- Now let's verify the postconditions for test4.
  apply And.intro;
  · exact fun ⟨ i, hi, hi' ⟩ => by rcases i with ( _ | _ | _ | _ | _ | _ | _ | i ) <;> trivial;
  · -- Now let's verify the postconditions for test4. We'll start with ensuring3.
    apply And.intro;
    · exact ⟨ by decide, by decide ⟩;
    · exists 0

-- test8
lemma test8_precondition :
  precondition test8_arr := by
  -- Let's verify each part of the precondition for test8_arr.
  constructor;
  · -- The array test8_arr has size 2, which satisfies the condition.
    simp [require1, test8_arr];
  · unfold require2 require3 require4 require5;
    unfold isSorted adjacentDiffAtLeastOne adjacentDiffAtMostTwo hasExactlyOneGap;
    -- Let's verify each part of the conjunction for the array [5, 7].
    simp [test8_arr];
    grind

lemma test8_postcondition :
  postcondition test8_arr test8_Expected := by
  unfold test8_arr test8_Expected;
  -- Let's verify the postconditions for the test case with array [5, 7] and missing number 6.
  constructor;
  · -- Show that 6 is not in the array [5, 7].
    simp [ensures1, inArray];
    decide;
  · aesop;
    · constructor <;> norm_num;
    · exists 0;

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (arr: Array Int):
  precondition arr →
  (∀ ret1 ret2,
    postcondition arr ret1 →
    postcondition arr ret2 →
    ret1 = ret2) := by
  bound;
  -- By definition of `postcondition`, if `ret1` and `ret2` both satisfy `postcondition arr`, then they must be equal to `arr[k]! + 1` for some `k`.
  obtain ⟨k1, hk1⟩ := a_1.right.right
  obtain ⟨k2, hk2⟩ := a_2.right.right;
  have := a.2.2.2.2.2 k1 k2; aesop;
