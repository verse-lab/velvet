import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000












def precondition (lst : List Int) :=
  True

def postcondition (lst : List Int) (result : Option Int) :=
  match result with
  | none =>

      ∀ j : Nat, j < lst.length → ¬((lst.take j).contains lst[j]!)
  | some x =>




      ∃ j : Nat, j < lst.length ∧
                 lst[j]! = x ∧
                 (lst.take j).contains x ∧
                 (∀ k : Nat, k < j → ¬((lst.take k).contains lst[k]!))


def test1_lst : List Int := [1, 2, 3, 2, 4]

def test1_Expected : Option Int := some 2

def test4_lst : List Int := [7, 7, 7, 7]

def test4_Expected : Option Int := some 7

def test6_lst : List Int := [-1, 2, -1]

def test6_Expected : Option Int := some (-1)







section Proof
theorem test1_precondition :
  precondition test1_lst := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_lst test1_Expected := by
  unfold postcondition test1_lst test1_Expected
  -- Need to prove the some case: ∃ j, j < 5 ∧ lst[j]! = 2 ∧ (lst.take j).contains 2 ∧ ∀ k < j, ¬...
  refine ⟨3, ?_, ?_, ?_, ?_⟩
  · -- 3 < 5
    native_decide
  · -- [1, 2, 3, 2, 4][3]! = 2
    native_decide
  · -- [1, 2, 3].contains 2
    native_decide
  · -- ∀ k < 3, ¬((lst.take k).contains lst[k]!)
    intro k hk
    interval_cases k
    · -- k = 0: ¬([].contains 1)
      native_decide
    · -- k = 1: ¬([1].contains 2)
      native_decide
    · -- k = 2: ¬([1, 2].contains 3)
      native_decide

theorem test4_precondition :
  precondition test4_lst := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_lst test4_Expected := by
  unfold postcondition test4_lst test4_Expected
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · intro k hk
    interval_cases k
    native_decide

theorem test6_precondition :
  precondition test6_lst := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_lst test6_Expected := by
  unfold postcondition test6_lst test6_Expected
  refine ⟨2, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · intro k hk
    interval_cases k <;> native_decide

theorem uniqueness (lst : List Int):
  precondition lst →
  (∀ ret1 ret2,
    postcondition lst ret1 →
    postcondition lst ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  cases ret1 with
  | none =>
    cases ret2 with
    | none => rfl
    | some x2 =>
      -- hpost1: ∀ j < lst.length, ¬((lst.take j).contains lst[j]!)
      -- hpost2: ∃ j < lst.length, lst[j]! = x2 ∧ (lst.take j).contains x2 ∧ ...
      obtain ⟨j2, hj2_lt, hj2_eq, hj2_contains, _⟩ := hpost2
      have h := hpost1 j2 hj2_lt
      rw [hj2_eq] at h
      exact absurd hj2_contains h
  | some x1 =>
    cases ret2 with
    | none =>
      -- hpost1: ∃ j < lst.length, lst[j]! = x1 ∧ (lst.take j).contains x1 ∧ ...
      -- hpost2: ∀ j < lst.length, ¬((lst.take j).contains lst[j]!)
      obtain ⟨j1, hj1_lt, hj1_eq, hj1_contains, _⟩ := hpost1
      have h := hpost2 j1 hj1_lt
      rw [hj1_eq] at h
      exact absurd hj1_contains h
    | some x2 =>
      -- Both are some, need to show x1 = x2
      obtain ⟨j1, hj1_lt, hj1_eq, hj1_contains, hj1_min⟩ := hpost1
      obtain ⟨j2, hj2_lt, hj2_eq, hj2_contains, hj2_min⟩ := hpost2
      -- Show j1 = j2 by trichotomy
      rcases Nat.lt_trichotomy j1 j2 with h_lt | h_eq | h_gt
      · -- j1 < j2: contradiction with hj2_min
        have h := hj2_min j1 h_lt
        rw [hj1_eq] at h
        exact absurd hj1_contains h
      · -- j1 = j2: then x1 = x2
        subst h_eq
        -- Now hj1_eq : lst[j1]! = x1 and hj2_eq : lst[j1]! = x2
        -- So x1 = lst[j1]! = x2
        have heq : x1 = x2 := by rw [← hj1_eq, ← hj2_eq]
        rw [heq]
      · -- j2 < j1: contradiction with hj1_min
        have h := hj1_min j2 h_gt
        rw [hj2_eq] at h
        exact absurd hj2_contains h
end Proof
