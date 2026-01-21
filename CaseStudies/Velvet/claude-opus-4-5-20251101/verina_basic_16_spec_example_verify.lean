import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (s : String) (oldChar : Char) (newChar : Char) :=
  True







def postcondition (s : String) (oldChar : Char) (newChar : Char) (result : String) :=
  result.length = s.length ∧
  ∀ i : Nat, i < s.length →
    (s.toList[i]! = oldChar → result.toList[i]! = newChar) ∧
    (s.toList[i]! ≠ oldChar → result.toList[i]! = s.toList[i]!)


def test1_s : String := "hello, world!"

def test1_oldChar : Char := ','

def test1_newChar : Char := ';'

def test1_Expected : String := "hello; world!"

def test3_s : String := "hello, world!"

def test3_oldChar : Char := 'o'

def test3_newChar : Char := 'O'

def test3_Expected : String := "hellO, wOrld!"

def test7_s : String := "aaa"

def test7_oldChar : Char := 'a'

def test7_newChar : Char := 'b'

def test7_Expected : String := "bbb"







section Proof
theorem test1_precondition :
  precondition test1_s test1_oldChar test1_newChar := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_oldChar test1_newChar test1_Expected := by
  unfold postcondition test1_s test1_oldChar test1_newChar test1_Expected
  native_decide

theorem test3_precondition :
  precondition test3_s test3_oldChar test3_newChar := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_s test3_oldChar test3_newChar test3_Expected := by
  unfold postcondition test3_s test3_oldChar test3_newChar test3_Expected
  native_decide

theorem test7_precondition :
  precondition test7_s test7_oldChar test7_newChar := by
  intros; expose_names; exact (trivial); done

theorem test7_postcondition_0 : postcondition test7_s test7_oldChar test7_newChar test7_Expected ↔ test7_Expected.length = test7_s.length ∧ ∀ i < test7_s.length, (test7_s.data[i]?.getD 'A' = test7_oldChar → test7_Expected.data[i]?.getD 'A' = test7_newChar) ∧ (¬test7_s.data[i]?.getD 'A' = test7_oldChar → test7_Expected.data[i]?.getD 'A' = test7_s.data[i]?.getD 'A') := by
    unfold postcondition test7_s test7_oldChar test7_newChar test7_Expected
    simp only [String.length, String.toList, List.length]
    constructor
    · intro ⟨hlen, hchars⟩
      constructor
      · exact hlen
      · intro i hi
        have h := hchars i hi
        simp only [List.getElem!_eq_getElem?_getD] at h
        exact h
    · intro ⟨hlen, hchars⟩
      constructor
      · exact hlen
      · intro i hi
        have h := hchars i hi
        simp only [List.getElem!_eq_getElem?_getD]
        exact h

theorem test7_postcondition_1
    (h2 : test7_Expected.length = test7_s.length)
    (h3 : test7_s.length = 3)
    (h1 : postcondition test7_s test7_oldChar test7_newChar test7_Expected ↔ test7_Expected.length = test7_s.length ∧ ∀ i < test7_s.length, (test7_s.data[i]?.getD 'A' = test7_oldChar → test7_Expected.data[i]?.getD 'A' = test7_newChar) ∧ (¬test7_s.data[i]?.getD 'A' = test7_oldChar → test7_Expected.data[i]?.getD 'A' = test7_s.data[i]?.getD 'A'))
    : ∀ i < 3, (test7_s.data[i]?.getD 'A' = test7_oldChar → test7_Expected.data[i]?.getD 'A' = test7_newChar) ∧ (¬test7_s.data[i]?.getD 'A' = test7_oldChar → test7_Expected.data[i]?.getD 'A' = test7_s.data[i]?.getD 'A') := by
    intro i hi
    unfold test7_s test7_oldChar test7_newChar test7_Expected
    simp only [String.data]
    interval_cases i <;> simp

theorem test7_postcondition :
  postcondition test7_s test7_oldChar test7_newChar test7_Expected := by
  have h1 : postcondition test7_s test7_oldChar test7_newChar test7_Expected ↔ 
    (test7_Expected.length = test7_s.length ∧
     ∀ i : Nat, i < test7_s.length →
       (test7_s.toList[i]! = test7_oldChar → test7_Expected.toList[i]! = test7_newChar) ∧
       (test7_s.toList[i]! ≠ test7_oldChar → test7_Expected.toList[i]! = test7_s.toList[i]!)) := by
    (try simp at *; expose_names); exact (test7_postcondition_0); done
  have h2 : test7_Expected.length = test7_s.length := by
    (try simp at *; expose_names); exact rfl; done
  have h3 : test7_s.length = 3 := by
    (try simp at *; expose_names); exact h2; done
  have h4 : ∀ i : Nat, i < 3 →
    (test7_s.toList[i]! = test7_oldChar → test7_Expected.toList[i]! = test7_newChar) ∧
    (test7_s.toList[i]! ≠ test7_oldChar → test7_Expected.toList[i]! = test7_s.toList[i]!) := by
    (try simp at *; expose_names); exact (test7_postcondition_1 h2 h3 h1); done
  have h5 : ∀ i : Nat, i < test7_s.length →
    (test7_s.toList[i]! = test7_oldChar → test7_Expected.toList[i]! = test7_newChar) ∧
    (test7_s.toList[i]! ≠ test7_oldChar → test7_Expected.toList[i]! = test7_s.toList[i]!) := by
    (try simp at *; expose_names); exact fun i a ↦ h4 i a; done
  unfold postcondition test7_s test7_oldChar test7_newChar test7_Expected
  native_decide

theorem uniqueness_0
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (_hpre : precondition s oldChar newChar)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition s oldChar newChar ret1)
    (hpost2 : postcondition s oldChar newChar ret2)
    : ret1.length = s.length := by
    unfold postcondition at hpost1
    exact hpost1.1

theorem uniqueness_1
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (_hpre : precondition s oldChar newChar)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition s oldChar newChar ret1)
    (hpost2 : postcondition s oldChar newChar ret2)
    (hlen1 : ret1.length = s.length)
    : ret2.length = s.length := by
    intros; expose_names; exact (uniqueness_0 s oldChar newChar _hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_2
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (_hpre : precondition s oldChar newChar)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition s oldChar newChar ret1)
    (hpost2 : postcondition s oldChar newChar ret2)
    (hlen1 : ret1.length = s.length)
    (hlen2 : ret2.length = s.length)
    : ret1.length = ret2.length := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_3
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (_hpre : precondition s oldChar newChar)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition s oldChar newChar ret1)
    (hpost2 : postcondition s oldChar newChar ret2)
    (hlen1 : ret1.length = s.length)
    (hlen2 : ret2.length = s.length)
    (hlen_eq : ret1.length = ret2.length)
    : ∀ i < s.length, (s.data[i]?.getD 'A' = oldChar → ret1.data[i]?.getD 'A' = newChar) ∧ (¬s.data[i]?.getD 'A' = oldChar → ret1.data[i]?.getD 'A' = s.data[i]?.getD 'A') := by
    intro i hi
    have hpost1' := hpost1.2 i hi
    have hs_len : i < s.data.length := by simp [String.length] at hi; exact hi
    have hret1_len : i < ret1.data.length := by simp [String.length] at hlen1; omega
    -- Connect s.toList with s.data
    have hs_toList : s.toList = s.data := rfl
    -- For valid index, getElem? returns some
    have hs_get : s.data[i]? = some s.data[i] := List.getElem?_eq_getElem hs_len
    have hret1_get : ret1.data[i]? = some ret1.data[i] := List.getElem?_eq_getElem hret1_len
    -- getD of some equals the value
    have hs_getD : s.data[i]?.getD 'A' = s.data[i] := by rw [hs_get]; rfl
    have hret1_getD : ret1.data[i]?.getD 'A' = ret1.data[i] := by rw [hret1_get]; rfl
    -- Connect getElem! to actual element
    have hs_bang : s.toList[i]! = s.data[i] := by
      simp only [hs_toList]
      rw [List.getElem!_eq_getElem?_getD, hs_get]
      rfl
    have hret1_bang : ret1.toList[i]! = ret1.data[i] := by
      have : ret1.toList = ret1.data := rfl
      simp only [this]
      rw [List.getElem!_eq_getElem?_getD, hret1_get]
      rfl
    constructor
    · intro h_eq
      rw [hs_getD] at h_eq
      rw [hret1_getD]
      have : s.toList[i]! = oldChar := by rw [hs_bang]; exact h_eq
      have := hpost1'.1 this
      rw [hret1_bang] at this
      exact this
    · intro h_neq
      rw [hs_getD] at h_neq
      rw [hret1_getD, hs_getD]
      have : s.toList[i]! ≠ oldChar := by rw [hs_bang]; exact h_neq
      have := hpost1'.2 this
      rw [hret1_bang, hs_bang] at this
      exact this

theorem uniqueness_4
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (_hpre : precondition s oldChar newChar)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition s oldChar newChar ret1)
    (hpost2 : postcondition s oldChar newChar ret2)
    (hlen1 : ret1.length = s.length)
    (hlen2 : ret2.length = s.length)
    (hlen_eq : ret1.length = ret2.length)
    (hchars1 : ∀ i < s.length, (s.data[i]?.getD 'A' = oldChar → ret1.data[i]?.getD 'A' = newChar) ∧ (¬s.data[i]?.getD 'A' = oldChar → ret1.data[i]?.getD 'A' = s.data[i]?.getD 'A'))
    : ∀ i < s.length, (s.data[i]?.getD 'A' = oldChar → ret2.data[i]?.getD 'A' = newChar) ∧ (¬s.data[i]?.getD 'A' = oldChar → ret2.data[i]?.getD 'A' = s.data[i]?.getD 'A') := by
    intros; expose_names; exact (uniqueness_3 s oldChar newChar _hpre ret2 ret1 hpost2 hpost1 hlen2 hlen1 (id (Eq.symm hlen_eq)) i h); done

theorem uniqueness_5
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (_hpre : precondition s oldChar newChar)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition s oldChar newChar ret1)
    (hpost2 : postcondition s oldChar newChar ret2)
    (hlen1 : ret1.length = s.length)
    (hlen2 : ret2.length = s.length)
    (hlen_eq : ret1.length = ret2.length)
    (hlist_len1 : ret1.data.length = s.length)
    (hlist_len2 : ret2.data.length = s.length)
    (hlist_len_eq : ret1.data.length = ret2.data.length)
    (hchars1 : ∀ i < s.length, (s.data[i]?.getD 'A' = oldChar → ret1.data[i]?.getD 'A' = newChar) ∧ (¬s.data[i]?.getD 'A' = oldChar → ret1.data[i]?.getD 'A' = s.data[i]?.getD 'A'))
    (hchars2 : ∀ i < s.length, (s.data[i]?.getD 'A' = oldChar → ret2.data[i]?.getD 'A' = newChar) ∧ (¬s.data[i]?.getD 'A' = oldChar → ret2.data[i]?.getD 'A' = s.data[i]?.getD 'A'))
    : ∀ i < s.length, ret1.data[i]?.getD 'A' = ret2.data[i]?.getD 'A' := by
    intro i hi
    have h1 := hchars1 i hi
    have h2 := hchars2 i hi
    by_cases heq : s.data[i]?.getD 'A' = oldChar
    · -- Case: s.data[i] = oldChar
      have hr1 : ret1.data[i]?.getD 'A' = newChar := h1.1 heq
      have hr2 : ret2.data[i]?.getD 'A' = newChar := h2.1 heq
      rw [hr1, hr2]
    · -- Case: s.data[i] ≠ oldChar
      have hr1 : ret1.data[i]?.getD 'A' = s.data[i]?.getD 'A' := h1.2 heq
      have hr2 : ret2.data[i]?.getD 'A' = s.data[i]?.getD 'A' := h2.2 heq
      rw [hr1, hr2]

theorem uniqueness_6
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (_hpre : precondition s oldChar newChar)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition s oldChar newChar ret1)
    (hpost2 : postcondition s oldChar newChar ret2)
    (hlen1 : ret1.length = s.length)
    (hlen2 : ret2.length = s.length)
    (hlen_eq : ret1.length = ret2.length)
    (hlist_len1 : ret1.data.length = s.length)
    (hlist_len2 : ret2.data.length = s.length)
    (hlist_len_eq : ret1.data.length = ret2.data.length)
    (hchars1 : ∀ i < s.length, (s.data[i]?.getD 'A' = oldChar → ret1.data[i]?.getD 'A' = newChar) ∧ (¬s.data[i]?.getD 'A' = oldChar → ret1.data[i]?.getD 'A' = s.data[i]?.getD 'A'))
    (hchars2 : ∀ i < s.length, (s.data[i]?.getD 'A' = oldChar → ret2.data[i]?.getD 'A' = newChar) ∧ (¬s.data[i]?.getD 'A' = oldChar → ret2.data[i]?.getD 'A' = s.data[i]?.getD 'A'))
    (heq_at_each : ∀ i < s.length, ret1.data[i]?.getD 'A' = ret2.data[i]?.getD 'A')
    : ret1.data = ret2.data := by
    apply List.ext_getElem hlist_len_eq
    intro i h1 h2
    have hi_s : i < s.length := by omega
    have heq := heq_at_each i hi_s
    simp only [List.getD_getElem?, h1, h2, dite_true] at heq
    exact heq

theorem uniqueness (s : String) (oldChar : Char) (newChar : Char):
  precondition s oldChar newChar →
  (∀ ret1 ret2,
    postcondition s oldChar newChar ret1 →
    postcondition s oldChar newChar ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- Extract the components of the postconditions
  have hlen1 : ret1.length = s.length := by
    (try simp at *; expose_names); exact (uniqueness_0 s oldChar newChar _hpre ret1 ret2 hpost1 hpost2); done
  have hlen2 : ret2.length = s.length := by
    (try simp at *; expose_names); exact (uniqueness_1 s oldChar newChar _hpre ret1 ret2 hpost1 hpost2 hlen1); done
  have hlen_eq : ret1.length = ret2.length := by
    (try simp at *; expose_names); exact (uniqueness_2 s oldChar newChar _hpre ret1 ret2 hpost1 hpost2 hlen1 hlen2); done
  have hchars1 : ∀ i : Nat, i < s.length → (s.toList[i]! = oldChar → ret1.toList[i]! = newChar) ∧ (s.toList[i]! ≠ oldChar → ret1.toList[i]! = s.toList[i]!) := by
    (try simp at *; expose_names); exact (uniqueness_3 s oldChar newChar _hpre ret1 ret2 hpost1 hpost2 hlen1 hlen2 hlen_eq); done
  have hchars2 : ∀ i : Nat, i < s.length → (s.toList[i]! = oldChar → ret2.toList[i]! = newChar) ∧ (s.toList[i]! ≠ oldChar → ret2.toList[i]! = s.toList[i]!) := by
    (try simp at *; expose_names); exact (uniqueness_4 s oldChar newChar _hpre ret1 ret2 hpost1 hpost2 hlen1 hlen2 hlen_eq hchars1); done
  -- Show that the toList lengths are equal
  have hlist_len1 : ret1.toList.length = s.length := by
    (try simp at *; expose_names); exact hlen1; done
  have hlist_len2 : ret2.toList.length = s.length := by
    (try simp at *; expose_names); exact hlen2; done
  have hlist_len_eq : ret1.toList.length = ret2.toList.length := by
    (try simp at *; expose_names); exact hlen_eq; done
  -- Show that elements at each position are equal
  have heq_at_each : ∀ i : Nat, i < s.length → ret1.toList[i]! = ret2.toList[i]! := by
    (try simp at *; expose_names); exact (uniqueness_5 s oldChar newChar _hpre ret1 ret2 hpost1 hpost2 hlen1 hlen2 hlen_eq hlist_len1 hlist_len2 hlist_len_eq hchars1 hchars2); done
  -- Use List.ext_getElem to show the lists are equal
  have hlist_eq : ret1.toList = ret2.toList := by
    (try simp at *; expose_names); exact (uniqueness_6 s oldChar newChar _hpre ret1 ret2 hpost1 hpost2 hlen1 hlen2 hlen_eq hlist_len1 hlist_len2 hlist_len_eq hchars1 hchars2 heq_at_each); done
  -- Use String.ext_iff to conclude the strings are equal
  have hstr_ext : ret1 = ret2 ↔ ret1.toList = ret2.toList := by
    (try simp at *; expose_names); exact String.ext_iff; done
  exact hstr_ext.mpr hlist_eq
end Proof
