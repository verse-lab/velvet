import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (s : String) : Prop :=
  True



def postcondition (s : String) (result : String) : Prop :=

  result.length = s.length ∧

  (∀ i : Nat, i < s.length → result.data[i]! = s.data[i]!.toLower)


def test1_s : String := "Hello, World!"

def test1_Expected : String := "hello, world!"

def test2_s : String := "ABC"

def test2_Expected : String := "abc"

def test4_s : String := ""

def test4_Expected : String := ""







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition test1_s test1_Expected
  constructor
  · native_decide
  · intro i hi
    have h : "Hello, World!".length = 13 := by native_decide
    simp only [h] at hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | 3 => native_decide
    | 4 => native_decide
    | 5 => native_decide
    | 6 => native_decide
    | 7 => native_decide
    | 8 => native_decide
    | 9 => native_decide
    | 10 => native_decide
    | 11 => native_decide
    | 12 => native_decide
    | n + 13 => omega

theorem test2_precondition :
  precondition test2_s := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_s test2_Expected := by
  unfold postcondition test2_s test2_Expected
  constructor
  · native_decide
  · intro i hi
    have h : "ABC".length = 3 := by native_decide
    rw [h] at hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | n + 3 => omega

theorem test4_precondition :
  precondition test4_s := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_s test4_Expected := by
  unfold postcondition test4_s test4_Expected
  constructor
  · -- "".length = "".length
    rfl
  · -- ∀ i : Nat, i < "".length → "".data[i]! = "".data[i]!.toLower
    intro i hi
    -- "".length = 0, so i < 0 is impossible for Nat
    simp only [String.length] at hi
    exact absurd hi (Nat.not_lt_zero i)

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨hlen1, hchar1⟩ := hpost1
  obtain ⟨hlen2, hchar2⟩ := hpost2
  apply String.ext
  have hlen_eq : ret1.data.length = ret2.data.length := by
    simp only [String.length] at hlen1 hlen2
    omega
  apply List.ext_getElem hlen_eq
  intro i hi1 hi2
  have hs_len : i < s.length := by
    simp only [String.length] at hlen1 ⊢
    omega
  have h1 := hchar1 i hs_len
  have h2 := hchar2 i hs_len
  simp only [List.getElem!_eq_getElem?_getD] at h1 h2
  have hget1 : ret1.data[i]? = some ret1.data[i] := List.getElem?_eq_getElem hi1
  have hget2 : ret2.data[i]? = some ret2.data[i] := List.getElem?_eq_getElem hi2
  have hs_len' : i < s.data.length := by 
    simp only [String.length] at hs_len
    exact hs_len
  have hgets : s.data[i]? = some s.data[i] := List.getElem?_eq_getElem hs_len'
  simp only [hget1, hgets, Option.getD_some] at h1
  simp only [hget2, hgets, Option.getD_some] at h2
  rw [h1, h2]
end Proof
