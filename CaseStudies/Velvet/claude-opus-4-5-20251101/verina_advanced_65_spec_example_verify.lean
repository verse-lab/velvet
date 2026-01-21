import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (s : String) : Prop :=
  True




def postcondition (s : String) (result : String) : Prop :=
  let inputChars := s.toList
  let resultChars := result.toList

  resultChars.length = inputChars.length ∧

  (∀ i : Nat, i < inputChars.length →
    resultChars[i]! = inputChars[inputChars.length - 1 - i]!)


def test1_s : String := "hello"

def test1_Expected : String := "olleh"

def test2_s : String := "a"

def test2_Expected : String := "a"

def test3_s : String := ""

def test3_Expected : String := ""







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition test1_s test1_Expected
  constructor
  · rfl
  · intro i hi
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | n + 5 => simp only [String.toList, List.length] at hi; omega

theorem test2_precondition :
  precondition test2_s := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_s test2_Expected := by
  unfold postcondition test2_s test2_Expected
  simp only [String.toList]
  constructor
  · -- Length equality: both are 1, simplifies to True
    trivial
  · -- Reversal property
    intro i hi
    -- Since i < 1, we have i = 0
    have h : i = 0 := Nat.lt_one_iff.mp hi
    subst h
    native_decide

theorem test3_precondition :
  precondition test3_s := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
  unfold postcondition test3_s test3_Expected
  simp [String.toList]

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- Unfold postcondition to access its components
  simp only [postcondition] at hpost1 hpost2
  -- Extract the length and element-wise conditions
  obtain ⟨hlen1, helems1⟩ := hpost1
  obtain ⟨hlen2, helems2⟩ := hpost2
  -- Show ret1 = ret2 by showing their character lists are equal
  apply String.ext
  -- Show ret1.toList = ret2.toList using List.ext_getElem
  apply List.ext_getElem
  · -- Length equality: ret1.toList.length = ret2.toList.length
    -- Note: String.toList = String.data
    simp only [String.toList] at hlen1 hlen2
    omega
  · -- Element-wise equality
    intro i h1 h2
    -- We need to show ret1.data[i] = ret2.data[i]
    -- Note: String.toList = String.data
    simp only [String.toList] at hlen1 hlen2 helems1 helems2
    have hi_lt_s : i < s.data.length := by omega
    have h1' := helems1 i hi_lt_s
    have h2' := helems2 i hi_lt_s
    -- Both ret1.data[i]! and ret2.data[i]! equal s.data[s.data.length - 1 - i]!
    -- So they are equal to each other
    simp only [List.getElem!_eq_getElem?_getD] at h1' h2'
    -- Convert getElem? to getElem when in bounds
    have h1_bound : i < ret1.data.length := h1
    have h2_bound : i < ret2.data.length := h2
    simp only [List.getElem?_eq_getElem h1_bound, Option.getD_some] at h1'
    simp only [List.getElem?_eq_getElem h2_bound, Option.getD_some] at h2'
    have hs_idx : s.data.length - 1 - i < s.data.length := by omega
    simp only [List.getElem?_eq_getElem hs_idx, Option.getD_some] at h1' h2'
    rw [h1', h2']
end Proof
