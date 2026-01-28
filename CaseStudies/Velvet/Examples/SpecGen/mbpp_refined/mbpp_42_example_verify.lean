import Lean
import Mathlib.Tactic

-- Helper Functions

def isRepeated (arr : Array Int) (value : Int) : Bool :=
  arr.count value > 1

def sumOfRepeatedElements (arr : Array Int) : Int :=
  arr.foldl
  (fun acc x => if isRepeated arr x then acc + x else acc) 0

-- Postcondition clauses
def ensures1 (arr : Array Int) (sum : Int) :=
  sum = sumOfRepeatedElements arr

def precondition (arr: Array Int) :=
  True

def postcondition (arr: Array Int) (sum: Int) :=
  ensures1 arr sum

-- Test Cases
def test1_arr : Array Int := #[1, 2, 3, 1, 1, 4, 5, 6]

def test1_Expected : Int := 3

def test2_arr : Array Int := #[1, 2, 3, 1, 2]

def test2_Expected : Int := 6

def test3_arr : Array Int := #[1, 2, 3, 4]

def test3_Expected : Int := 0

def test4_arr : Array Int := #[5, 5, 5, 5]

def test4_Expected : Int := 20

def test5_arr : Array Int := #[]

def test5_Expected : Int := 0

def test8_arr : Array Int := #[-1, 2, -1, 3, 4, 2]

def test8_Expected : Int := 2

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_arr := by
  exact?

lemma test1_postcondition :
  postcondition test1_arr test1_Expected := by
  -- Now let's verify that the sum is indeed 3.
  simp [postcondition, test1_arr, ensures1];
  -- Let's calculate the sum of the repeated elements in the array.
  simp +decide

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_arr := by
  exact?

lemma test2_postcondition :
  postcondition test2_arr test2_Expected := by
  exact?

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_arr := by
  exact?

lemma test3_postcondition :
  postcondition test3_arr test3_Expected := by
  bound

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_arr := by
  exact?

lemma test4_postcondition :
  postcondition test4_arr test4_Expected := by
  bound

----------------------------
-- Verification: test5
----------------------------
lemma test5_precondition :
  precondition test5_arr := by
  exact?

lemma test5_postcondition :
  postcondition test5_arr test5_Expected := by
  exact?

----------------------------
-- Verification: test8
----------------------------
lemma test8_precondition :
  precondition test8_arr := by
  exact?

lemma test8_postcondition :
  postcondition test8_arr test8_Expected := by
  -- By definition of postcondition, we need to show that sumOfRepeatedElements test8_arr equals test8_Expected.
  apply Eq.symm; exact (by
  decide +kernel)

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
  -- Since both `ret1` and `ret2` are equal to `sumOfRepeatedElements arr`, they must be equal to each other.
  rw [a_1, a_2]
