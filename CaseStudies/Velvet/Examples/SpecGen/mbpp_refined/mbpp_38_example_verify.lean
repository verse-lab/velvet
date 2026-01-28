import Lean
import Mathlib.Tactic


-- Helper Functions

def isEven (n : Int) : Prop := ∃ k : Int, n = 2 * k

def isOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

def isFirstEven (lst : List Int) (i : Nat) : Prop :=
  i < lst.length ∧
  isEven lst[i]! ∧
  ∀ j, j < i → ¬isEven lst[j]!

def isFirstOdd (lst : List Int) (j : Nat) : Prop :=
  j < lst.length ∧
  isOdd lst[j]! ∧
  ∀ k, k < j → ¬isOdd lst[k]!

def require1 (lst : Array Int) :=
  ∃ x ∈ lst, isEven x

def require2 (lst : Array Int) :=
  ∃ x ∈ lst, isOdd x

-- Postcondition clauses
def ensures1 (lst : Array Int) (result : Rat) :=
  (∃ i j : Nat,
    isFirstEven lst.toList i ∧
    isFirstOdd lst.toList j ∧
    result = ((lst[i]! : Rat) / (lst[j]! : Rat)))

def precondition (lst: Array Int) :=
  True

def postcondition (lst: Array Int) (result: Rat) :=
  ensures1 lst result

-- Test case 0: Sample from the problem
def test0_Input : Array Int := #[1,3,5,7,4,1,6,8]

def test0_Expected : Rat := 4 / 1

-- Test case 1: Both even and odd present, even comes first
def test1_Input : Array Int := #[2, 3, 4, 5]

def test1_Expected : Rat := 2 / 3

-- Test case 2: Both even and odd present, odd comes first
def test2_Input : Array Int := #[1, 2, 3, 4]

def test2_Expected : Rat := 2 / 1

-- Test case 3: First even comes much later
def test3_Input : Array Int := #[1, 3, 5, 7, 2, 4]

def test3_Expected : Rat := 2 / 1

-- Test case 5: Large numbers
def test5_Input : Array Int := #[100, 201, 300, 401]

def test5_Expected : Rat := 100 / 201

-- Test case 6: Negative numbers
def test6_Input : Array Int := #[-4, -3, -2, -1]

def test6_Expected : Rat := 4 / 3

-------------------------------
-- Verifications
-------------------------------

-- test0
lemma test0_precondition :
  precondition test0_Input := by
  exact?

lemma test0_postcondition :
  postcondition test0_Input test0_Expected := by
  -- Verify that 4 is the first even number and 1 is the first odd number in the list.
  have h_even : isFirstEven [1, 3, 5, 7, 4, 1, 6, 8] 4 := by
    -- Check that 4 is even and that all elements before it are odd.
    simp [isFirstEven, isEven];
    exact ⟨ ⟨ 2, by norm_num ⟩, by intro j hj x hx; interval_cases j <;> norm_num at hx <;> omega ⟩
  have h_odd : isFirstOdd [1, 3, 5, 7, 4, 1, 6, 8] 0 := by
    -- The first element of the list is 1, which is odd.
    simp [isFirstOdd];
    exact ⟨ 0, rfl ⟩;
  exact ⟨ 4, 0, h_even, h_odd, by trivial ⟩

-- test1
lemma test1_precondition :
  precondition test1_Input := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test1_postcondition :
  postcondition test1_Input test1_Expected := by
  -- Let's simplify the goal. We need to show that the first even number is 2 and the first odd number is 3.
  have h_even : isFirstEven [2, 3, 4, 5] 0 := by
    constructor <;> norm_num;
    exact ⟨ 1, rfl ⟩
  have h_odd : isFirstOdd [2, 3, 4, 5] 1 := by
    -- We need to show that 3 is odd and that there are no odd numbers before it.
    simp [isFirstOdd, isOdd];
    exact ⟨ ⟨ 1, rfl ⟩, fun x hx => by linarith [ show x = 0 by linarith ] ⟩;
  exact ⟨ 0, 1, h_even, h_odd, by native_decide ⟩

-- test2
lemma test2_precondition :
  precondition test2_Input := by
  exact?

lemma test2_postcondition :
  postcondition test2_Input test2_Expected := by
  constructor;
  -- Let's choose the index of the first even number in the list.
  use 0;
  constructor;
  swap;
  constructor;
  exact ⟨ by decide, ⟨ 0, rfl ⟩, by simp +decide ⟩;
  rotate_right;
  exact 1;
  · decide +kernel;
  · unfold isFirstEven; simp +decide ;
    exact ⟨ ⟨ 1, rfl ⟩, fun ⟨ k, hk ⟩ => by norm_num [ test2_Input ] at hk; omega ⟩

-- test5
lemma test5_precondition :
  precondition test5_Input := by
  exact?

lemma test5_postcondition :
  postcondition test5_Input test5_Expected := by
  use 0, 1; simp +decide [ isFirstEven, isFirstOdd ] ;
  -- We can verify that 100 is even and 201 is odd.
  have h_even : isEven 100 := by
    exact ⟨ 50, by norm_num ⟩
  have h_odd : isOdd 201 := by
    -- We can verify that 201 is odd by definition.
    use 100
    norm_num
  exact ⟨h_even, ⟨h_odd, by
    unfold isOdd; norm_num;
    exact fun x hx => by norm_num [ test5_Input ] at hx; omega;⟩, rfl⟩

-- test11
lemma test6_precondition :
  precondition test6_Input := by
  trivial

lemma test6_postcondition :
  postcondition test6_Input test6_Expected := by
  unfold postcondition;
  unfold ensures1;
  unfold test6_Input test6_Expected; norm_num;
  use 0, by
    unfold isFirstEven; norm_num;
    exact ⟨ -2, by norm_num ⟩, 1, by
    -- Check that 1 is less than the length of the list.
    simp [isFirstOdd];
    exact ⟨ ⟨ -2, by norm_num ⟩, by rintro ⟨ k, hk ⟩ ; linarith [ show k = -2 by linarith ] ⟩;
  native_decide +revert

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (lst: Array Int):
  precondition lst →
  (∀ ret1 ret2,
    postcondition lst ret1 →
    postcondition lst ret2 →
    ret1 = ret2) := by
  -- By the definition of postcondition, if ret1 and ret2 are both postconditions of lst, then there exist indices i and j for ret1, and indices i' and j' for ret2, such that the fractions are formed by the first even and first odd elements in the list.
  intros h_pre ret1 ret2 h_ret1 h_ret2
  obtain ⟨i, j, hi, hj, h_frac1⟩ := h_ret1
  obtain ⟨i', j', hi', hj', h_frac2⟩ := h_ret2;
  -- Since $i$ and $i'$ are both indices of the first even element, they must be equal. Similarly, $j$ and $j'$ must be equal.
  have h_eq_i : i = i' := by
    have := hi.2.2;
    exact le_antisymm ( not_lt.mp fun contra => this _ contra hi'.2.1 ) ( not_lt.mp fun contra => hi'.2.2 _ contra hi.2.1 )
  have h_eq_j : j = j' := by
    unfold isFirstOdd at hj hj';
    grind;
  aesop
