import Lean
import Mathlib.Tactic

-- Helper Functions

def arraySum (arr: Array Int) : Int :=
  arr.foldl (· + ·) 0

def isAchievable (val: Int) (arrays: Array (Array Int)) : Prop :=
  ∃ i, i < arrays.size ∧ arraySum arrays[i]! = val

def isMaximal (val: Int) (arrays: Array (Array Int)) : Prop :=
  ∀ i, i < arrays.size → arraySum arrays[i]! ≤ val

def require1 (arrays : Array (Array Int)) :=
  arrays.size > 0  -- Need at least one inner array
  -- The result must be the sum of at least one inner array (achievability)

-- Postcondition clauses

def ensures1 (arrays : Array (Array Int)) (maxSum : Int) :=
  isAchievable maxSum arrays
def ensures2 (arrays : Array (Array Int)) (maxSum : Int) :=
  isMaximal maxSum arrays

def precondition (arrays: Array (Array Int)) :=
  require1 arrays

def postcondition (arrays: Array (Array Int)) (maxSum: Int) :=
  ensures1 arrays maxSum ∧ ensures2 arrays maxSum

-- Test Cases
def test1_arrays : Array (Array Int) := #[#[1,2,3], #[4,5,6], #[10,11,12], #[7,8,9]]

def test1_Expected : Int := 33

def test2_arrays : Array (Array Int) := #[#[1, 2, 3], #[4, 5], #[6]]

def test2_Expected : Int := 9

def test4_arrays : Array (Array Int) := #[#[-1, -2], #[-3, -4, -5], #[-10]]

def test4_Expected : Int := -3

def test5_arrays : Array (Array Int) := #[#[1, 2, 3, 4, 5]]

def test5_Expected : Int := 15

def test6_arrays : Array (Array Int) := #[#[1, 2], #[], #[3, 4, 5]]

def test6_Expected : Int := 12

def test8_arrays : Array (Array Int) := #[#[0, 0, 0], #[1, -1], #[2, 3]]

def test8_Expected : Int := 5

-------------------------------
-- Verifications
-------------------------------

-- test1
lemma test1_precondition :
  precondition test1_arrays := by
  -- The size of the test1_arrays is 4, which is greater than 0.
  simp [precondition, test1_arrays];
  -- The size of the test1_arrays is 4, which is greater than 0. Therefore, the require1 condition holds.
  simp [require1]

lemma test1_postcondition :
  postcondition test1_arrays test1_Expected := by
  -- We can verify that 33 is achievable by checking the sum of the third inner array.
  have h_ac: isAchievable 33 test1_arrays := by
    -- We know that the sum of the elements in the array #[10, 11, 12] is indeed 33.
    use 2; simp [test1_arrays, arraySum];
  -- To prove maximality, we need to show that for every inner array in test1_arrays, the sum of its elements is less than or equal to 33.
  have h_max : ∀ i, i < test1_arrays.size → arraySum test1_arrays[i]! ≤ 33 := by
    native_decide;
  -- Combine the achievability and maximality conditions to conclude the proof.
  apply And.intro h_ac h_max

-- test2
lemma test2_precondition :
  precondition test2_arrays := by
  exact Nat.succ_pos _

lemma test2_postcondition :
  postcondition test2_arrays test2_Expected := by
  -- Let's verify the postcondition for test2.
  apply And.intro;
  · -- Show that the sum of the second array is 9.
    use 1
    simp [test2_arrays];
    rfl;
  · -- We need to show that for any inner array, its sum is less than or equal to 9.
    intro i hi
    aesop;
    decide +revert

-- test4
lemma test4_precondition :
  precondition test4_arrays := by
  exact Nat.le_add_left _ _

lemma test4_postcondition :
  postcondition test4_arrays test4_Expected := by
  -- To prove the postcondition, we need to show that -3 is achievable and maximal.
  apply And.intro;
  · -- Show that -3 is achievable by finding an inner array whose sum is -3.
    use 0; simp [test4_arrays, test4_Expected];
    bound;
  · -- To prove the postcondition, we need to show that -3 is maximal.
    intros i hi
    aesop;
    native_decide +revert

-- test5
lemma test5_precondition :
  precondition test5_arrays := by
  -- The size of `test5_arrays` is 1, which is greater than 0.
  simp [precondition, test5_arrays];
  unfold require1; native_decide

lemma test5_postcondition :
  postcondition test5_arrays test5_Expected := by
  constructor;
  · -- The sum of the inner array #[1, 2, 3, 4, 5] is indeed 15.
    use 0
    simp [test5_arrays, test5_Expected];
    rfl;
  · -- The sum of the inner array [1, 2, 3, 4, 5] is 15, which is the maximum sum in this case.
    intros i hi
    aesop;
    decide +revert

-- test6
lemma test6_precondition :
  precondition test6_arrays := by
  exact Nat.zero_lt_succ _

lemma test6_postcondition :
  postcondition test6_arrays test6_Expected := by
  -- Show that 12 is achievable by the third inner array.
  have h_achievable : ∃ i, i < test6_arrays.size ∧ arraySum test6_arrays[i]! = 12 := by
    -- The third inner array is #[3,4,5], and its sum is 3 + 4 + 5 = 12.
    use 2; simp [test6_arrays, arraySum];
  -- Show that 12 is maximal by checking each inner array.
  have h_maximal : ∀ i, i < test6_arrays.size → arraySum test6_arrays[i]! ≤ 12 := by
    native_decide;
  -- Combine the achievability and maximality conditions to conclude the postcondition.
  apply And.intro h_achievable h_maximal

-- test8
lemma test8_precondition :
  precondition test8_arrays := by
  -- The size of `test8_arrays` is 3, which is greater than 0.
  simp [precondition, test8_arrays];
  -- The size of `test8_arrays` is 3, which is greater than 0. Therefore, the require1 condition holds.
  simp [require1]

lemma test8_postcondition :
  postcondition test8_arrays test8_Expected := by
  -- Let's choose i=2, which corresponds to the array [2,3].
  use ⟨2, by decide, by decide⟩;
  -- Let's verify the maximality condition for each element in the array.
  intros i hi
  simp [test8_arrays, test8_Expected] at *;
  -- Let's verify each case for i < 3.
  interval_cases i <;> simp +decide [arraySum]

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (arrays: Array (Array Int)):
  precondition arrays →
  (∀ ret1 ret2,
    postcondition arrays ret1 →
    postcondition arrays ret2 →
    ret1 = ret2) := by
  -- By definition of postcondition, if both ret1 and ret2 satisfy the postcondition, then they must be equal.
  intros h_pre ret1 ret2 h_ret1 h_ret2
  obtain ⟨i, hi⟩ := h_ret1.left
  obtain ⟨j, hj⟩ := h_ret2.left
  have h_max1 : ret1 ≥ ret2 := by
    linarith [ h_ret1.2 j hj.1, h_ret2.2 i hi.1 ]
  have h_max2 : ret2 ≥ ret1 := by
    linarith [ h_ret2.2 i hi.1 ]
  exact le_antisymm h_max2 h_max1
