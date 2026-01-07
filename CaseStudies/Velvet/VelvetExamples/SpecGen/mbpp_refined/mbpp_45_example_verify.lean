import Lean
import Mathlib.Tactic

-- Helper Functions

def dividesAll (d: Nat) (arr: Array Nat) : Prop :=
  ∀ i, i < arr.size → d ∣ arr[i]!

def isMaximalDivisor (d: Nat) (arr: Array Nat) : Prop :=
  dividesAll d arr ∧ (∀ d', dividesAll d' arr → d' ≤ d)

def require1 (arr : Array Nat) :=
  arr.size > 0
def require2 (arr : Array Nat) :=
  ∃ i, i < arr.size ∧ arr[i]! > 0   -- At least one non-zero element

-- Postcondition clauses

def ensures1 (arr : Array Nat) (result : Nat) :=
  dividesAll result arr
def ensures2 (arr : Array Nat) (result : Nat) :=
  ∀ d, dividesAll d arr → d ≤ result

def precondition (arr: Array Nat) :=
  require1 arr ∧ require2 arr

def postcondition (arr: Array Nat) (result: Nat) :=
  ensures1 arr result ∧ ensures2 arr result

-- Test Cases
def test1_arr : Array Nat := #[2, 4, 6, 8, 16]

def test1_Expected : Nat := 2

def test2_arr : Array Nat := #[42]

def test2_Expected : Nat := 42

def test3_arr : Array Nat := #[13, 17]

def test3_Expected : Nat := 1

def test4_arr : Array Nat := #[5, 5, 5, 5]

def test4_Expected : Nat := 5

def test5_arr : Array Nat := #[16, 32, 64, 128]

def test5_Expected : Nat := 16

def test15_arr : Array Nat := #[0, 12, 0, 6]

def test15_Expected : Nat := 6

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_arr := by
  -- We need to show that the precondition holds for the given array. Since the array is non-empty and contains at least one non-zero element, the precondition is satisfied. We can verify this by checking the size and the elements.
  simp [precondition, require1, require2];
  decide

lemma test1_postcondition :
  postcondition test1_arr test1_Expected := by
  -- We need to show that 2 divides all elements in the array and that it's the maximal such divisor.
  apply And.intro;
  · intro i hi;
    decide +revert;
  · -- To prove the second part, we need to show that any divisor of the array must be less than or equal to 2.
    intro d hd
    have h_div : d ∣ 2 := by
      exact hd 0 ( by decide ) |> Nat.dvd_trans <| by decide;
    -- Since $d$ divides $2$, the possible values for $d$ are $1$ or $2$. Therefore, $d \leq 2$.
    apply Nat.le_of_dvd (by norm_num) h_div

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_arr := by
  -- The array [42] is non-empty and contains a non-zero element, so the precondition holds.
  simp [precondition, test2_arr];
  -- The array [42] is non-empty and contains a non-zero element, so the precondition holds. We can use `test2_arr` which is defined as #[42].
  simp [require1, require2, test2_arr]

lemma test2_postcondition :
  postcondition test2_arr test2_Expected := by
  -- Show that 42 divides the only element in the array.
  have h_div : dividesAll 42 test2_arr := by
    -- Since the array has only one element, 42, the divisibility condition is trivially satisfied.
    simp [dividesAll, test2_arr];
  -- Show that 42 is the maximum divisor of the array.
  have h_max : ∀ d, dividesAll d test2_arr → d ≤ 42 := by
    -- Since the array contains only one element, 42, any divisor d of 42 must satisfy d ≤ 42.
    intros d hd
    have h_div_42 : d ∣ 42 := by
      -- Since the array has only one element, which is 42, any divisor d of 42 must satisfy d ≤ 42. Therefore, we can conclude that d divides 42.
      apply hd 0 (by decide)
    exact Nat.le_of_dvd (by norm_num) h_div_42;
  -- Combine the results to conclude the proof.
  apply And.intro h_div h_max

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_arr := by
  -- Check that the array is non-empty and has at least one non-zero element.
  simp [precondition, require1, require2];
  decide

lemma test3_postcondition :
  postcondition test3_arr test3_Expected := by
  -- To prove the postcondition, we need to show that 1 divides all elements in the array and that any other common divisor is less than or equal to 1.
  apply And.intro;
  · -- We can verify that 1 divides both 13 and 17.
    intro i hi
    aesop;
    native_decide +revert;
  · -- To prove the second part, we need to show that for any common divisor d of 13 and 17, d is less than or equal to 1.
    intro d hd
    have h_div13 : d ∣ 13 := by
      exact hd 0 ( by decide )
    have h_div17 : d ∣ 17 := by
      -- Since $d$ divides all elements in the array $test3_arr$, and $test3_arr$ contains $17$, we have $d \mid 17$.
      apply hd 1 (by decide)
    have h_gcd : Nat.gcd 13 17 = 1 := by
      -- The gcd of 13 and 17 is 1 because they are coprime.
      norm_num [Nat.gcd_comm, Nat.gcd_assoc] at *
    have h_d_le_1 : d ≤ 1 := by
      exact Nat.le_of_dvd ( by decide ) ( h_gcd ▸ Nat.dvd_gcd h_div13 h_div17 )
    exact h_d_le_1

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_arr := by
  -- Show that the array is non-empty and has at least one non-zero element.
  simp [precondition, test4_arr];
  -- The array is non-empty and contains at least one non-zero element.
  simp [require1, require2];
  decide +revert

lemma test4_postcondition :
  postcondition test4_arr test4_Expected := by
  -- Show that 5 divides all elements in the array [5, 5, 5, 5].
  have h_div : dividesAll 5 test4_arr := by
    -- Since the array is #[5, 5, 5, 5], every element is 5, and thus 5 divides each element.
    simp [dividesAll, test4_arr];
    native_decide;
  -- Show that 5 is the largest divisor of all elements in the array [5, 5, 5, 5].
  have h_max : ∀ d, dividesAll d test4_arr → d ≤ 5 := by
    exact fun d hd => Nat.le_of_dvd ( by decide ) ( hd 0 ( by decide ) );
  exact ⟨ h_div, h_max ⟩

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_arr := by
  constructor;
  · -- The array test5_arr has four elements, so its size is 4, which is greater than 0.
    simp [require1, test5_arr];
  · exact ⟨ 1, by decide, by decide ⟩

lemma test5_postcondition :
  postcondition test5_arr test5_Expected := by
  -- Show that 16 divides all elements in the array.
  have h_divides : ∀ i, i < test5_arr.size → 16 ∣ test5_arr[i]! := by
    native_decide +revert;
  -- Now, we need to show that any other common divisor is less than or equal to 16.
  have h_max : ∀ d, (∀ i, i < test5_arr.size → d ∣ test5_arr[i]!) → d ≤ 16 := by
    -- Since 16 is one of the elements in the array, any common divisor d must divide 16. Therefore, d ≤ 16.
    intros d hd
    have h_div_16 : d ∣ 16 := by
      exact hd 0 ( by decide );
    -- Since $d$ divides $16$, we have $d \leq 16$ by the definition of divisibility.
    apply Nat.le_of_dvd (by decide) h_div_16;
  exact ⟨ h_divides, h_max ⟩

----------------------------
-- Verification: test15
----------------------------
lemma test15_precondition :
  precondition test15_arr := by
  constructor;
  · -- The size of the array test15_arr is 4, which is greater than 0.
    simp [require1, test15_arr];
  · exists 1

lemma test15_postcondition :
  postcondition test15_arr test15_Expected := by
  -- Show that 6 divides all elements in the array [0, 12, 0, 6].
  have h_div : dividesAll 6 test15_arr := by
    -- We can verify that 6 divides each element in the array [0, 12, 0, 6].
    intro i hi
    aesop;
    native_decide +revert;
  -- Show that no number larger than 6 divides all elements in the array.
  have h_max : ∀ d, dividesAll d test15_arr → d ≤ 6 := by
    -- Since $d$ divides 6, we have $d \leq 6$ by the definition of divisibility.
    intros d hd
    have h_div_6 : d ∣ 6 := by
      exact hd 3 ( by decide );
    -- Since $d$ divides $6$, we have $d \leq 6$ by the definition of divisibility.
    apply Nat.le_of_dvd (by decide) h_div_6;
  -- Combine the results to conclude the postcondition.
  apply And.intro h_div h_max

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (arr: Array Nat):
  precondition arr →
  (∀ ret1 ret2,
    postcondition arr ret1 →
    postcondition arr ret2 →
    ret1 = ret2) := by
  -- If two numbers are both maximum divisors, they must be equal.
  intros h_pre ret1 ret2 h_ret1 h_ret2
  have h_le : ret1 ≤ ret2 ∧ ret2 ≤ ret1 := by
    exact ⟨ h_ret2.2 ret1 h_ret1.1, h_ret1.2 ret2 h_ret2.1 ⟩;
  -- By the antisymmetry of the ≤ relation, if ret1 ≤ ret2 and ret2 ≤ ret1, then ret1 = ret2.
  apply le_antisymm h_le.left h_le.right
