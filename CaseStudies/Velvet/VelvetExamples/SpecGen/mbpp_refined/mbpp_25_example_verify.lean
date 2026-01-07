import Lean
import Mathlib.Tactic

-- Helper Functions

-- Helper Functions
def productOfNonRepeatedElements (arr : Array Int) : Int :=
  arr.foldl
    (fun acc x => if arr.count x = 1 then acc * x else acc)
    1

-- Postcondition clauses
def ensures1 (arr : Array Int) (product : Int) :=
  product = productOfNonRepeatedElements arr

def precondition (arr: Array Int) :=
  True

def postcondition (arr: Array Int) (product: Int) :=
  ensures1 arr product

-- Test Cases
def test0_arr : Array Int := #[1, 1, 2, 3]

def test0_Expected : Int := 6

def test1_arr : Array Int := #[1, 2, 3, 2]

def test1_Expected : Int := 3

def test4_arr : Array Int := #[]

def test4_Expected : Int := 1

def test5_arr : Array Int := #[4, 5, 6]

def test5_Expected : Int := 120

def test7_arr : Array Int := #[0, 1, 2, 1]

def test7_Expected : Int := 0

def test8_arr : Array Int := #[-3, 5, 7, 5]

def test8_Expected : Int := -21

-------------------------------
-- Verifications
-------------------------------

-- test0
lemma test0_precondition :
  precondition test0_arr := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test0_postcondition :
  postcondition test0_arr test0_Expected := by
  rfl

-- test1
lemma test1_precondition :
  precondition test1_arr := by
  exact?

lemma test1_postcondition :
  postcondition test1_arr test1_Expected := by
  rfl

-- test4
lemma test4_precondition :
  precondition test4_arr := by
  trivial

lemma test4_postcondition :
  postcondition test4_arr test4_Expected := by
  rfl

-- test5
lemma test5_precondition :
  precondition test5_arr := by
  trivial

lemma test5_postcondition :
  postcondition test5_arr test5_Expected := by
  rfl

-- test7
lemma test7_precondition :
  precondition test7_arr := by
  exact?

lemma test7_postcondition :
  postcondition test7_arr test7_Expected := by
  rfl

-- test8
lemma test8_precondition :
  precondition test8_arr := by
  -- The precondition is trivially true for any array.
  simp [precondition]

lemma test8_postcondition :
  postcondition test8_arr test8_Expected := by
  rfl

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (arr: Array Int):
  precondition arr →
  (∀ ret1 ret2,
    postcondition arr ret1 →
    postcondition arr ret2 →
    ret1 = ret2) := by
  intro h1 ret1 ret2 h2 h3; unfold postcondition ensures1 at *;
  rw [h2, h3]
