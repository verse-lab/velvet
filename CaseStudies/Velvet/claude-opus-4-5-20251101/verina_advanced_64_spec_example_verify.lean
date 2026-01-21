import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def ensures1 (lst : List Nat) (target : Nat) (result : List Nat) :=
  target ∉ result


def ensures2 (lst : List Nat) (target : Nat) (result : List Nat) :=
  ∀ x, x ∈ result → x ∈ lst


def ensures3 (lst : List Nat) (target : Nat) (result : List Nat) :=
  ∀ x, x ∈ lst → x ≠ target → x ∈ result


def ensures4 (lst : List Nat) (target : Nat) (result : List Nat) :=
  result.Sublist lst


def ensures5 (lst : List Nat) (target : Nat) (result : List Nat) :=
  ∀ x, x ≠ target → result.count x = lst.count x

def precondition (lst : List Nat) (target : Nat) :=
  True

def postcondition (lst : List Nat) (target : Nat) (result : List Nat) :=
  ensures1 lst target result ∧
  ensures2 lst target result ∧
  ensures3 lst target result ∧
  ensures4 lst target result ∧
  ensures5 lst target result


def test1_lst : List Nat := [1, 2, 3, 2, 4]

def test1_target : Nat := 2

def test1_Expected : List Nat := [1, 3, 4]

def test2_lst : List Nat := [5, 5, 5, 5]

def test2_target : Nat := 5

def test2_Expected : List Nat := []

def test5_lst : List Nat := [0, 1, 0, 2, 0]

def test5_target : Nat := 0

def test5_Expected : List Nat := [1, 2]







section Proof
theorem test1_precondition :
  precondition test1_lst test1_target := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_lst test1_target test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 ensures5 test1_lst test1_target test1_Expected
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · intro x hx; fin_cases hx <;> simp
  · intro x hx hne; fin_cases hx <;> simp_all
  · native_decide
  · intro x hne
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> simp_all

theorem test2_precondition :
  precondition test2_lst test2_target := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_lst test2_target test2_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 ensures5
  unfold test2_lst test2_target test2_Expected
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ensures1: 5 ∉ []
    exact List.not_mem_nil
  · -- ensures2: ∀ x, x ∈ [] → x ∈ [5, 5, 5, 5]
    intro x hx
    exact absurd hx List.not_mem_nil
  · -- ensures3: ∀ x, x ∈ [5, 5, 5, 5] → x ≠ 5 → x ∈ []
    intro x hx hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    cases hx with
    | inl h => exact absurd h hne
    | inr h =>
      cases h with
      | inl h => exact absurd h hne
      | inr h =>
        cases h with
        | inl h => exact absurd h hne
        | inr h => exact absurd h hne
  · -- ensures4: [].Sublist [5, 5, 5, 5]
    exact List.nil_sublist _
  · -- ensures5: ∀ x, x ≠ 5 → [].count x = [5, 5, 5, 5].count x
    intro x hne
    simp only [List.count_nil, List.count_cons]
    have h1 : (5 == x) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun h => hne h.symm
    simp only [h1, ite_false, add_zero]
    rfl

theorem test5_precondition :
  precondition test5_lst test5_target := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition :
  postcondition test5_lst test5_target test5_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 ensures5
  unfold test5_lst test5_target test5_Expected
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ensures1: 0 ∉ [1, 2]
    simp [List.mem_cons]
  · -- ensures2: ∀ x, x ∈ [1, 2] → x ∈ [0, 1, 0, 2, 0]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp [List.mem_cons]
    · simp [List.mem_cons]
  · -- ensures3: ∀ x, x ∈ [0, 1, 0, 2, 0] → x ≠ 0 → x ∈ [1, 2]
    intro x hx hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · contradiction
    · simp [List.mem_cons]
    · contradiction
    · simp [List.mem_cons]
    · contradiction
  · -- ensures4: [1, 2] <+ [0, 1, 0, 2, 0]
    apply List.Sublist.cons
    apply List.Sublist.cons₂
    apply List.Sublist.cons
    apply List.Sublist.cons₂
    apply List.Sublist.cons
    exact List.Sublist.slnil
  · -- ensures5: ∀ x, x ≠ 0 → count x [1, 2] = count x [0, 1, 0, 2, 0]
    intro x hne
    simp only [List.count_cons, List.count_nil]
    by_cases h1 : 1 = x
    · subst h1
      simp
    · by_cases h2 : 2 = x
      · subst h2
        simp
      · have hx0 : (0 == x) = false := by simp [beq_eq_false_iff_ne]; omega
        have hx1 : (1 == x) = false := by simp [beq_eq_false_iff_ne, h1]
        have hx2 : (2 == x) = false := by simp [beq_eq_false_iff_ne, h2]
        simp [hx0, hx1, hx2]

theorem uniqueness_0
    (lst : List ℕ)
    (target : ℕ)
    (hpre : precondition lst target)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition lst target ret1)
    (hpost2 : postcondition lst target ret2)
    : ensures1 lst target ret1 := by
    exact hpost1.1

theorem uniqueness_1
    (lst : List ℕ)
    (target : ℕ)
    (hpre : precondition lst target)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition lst target ret1)
    (hpost2 : postcondition lst target ret2)
    (h1_e1 : ensures1 lst target ret1)
    : ensures4 lst target ret1 := by
    exact hpost1.2.2.2.1

theorem uniqueness_2
    (lst : List ℕ)
    (target : ℕ)
    (hpre : precondition lst target)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition lst target ret1)
    (hpost2 : postcondition lst target ret2)
    (h1_e1 : ensures1 lst target ret1)
    (h1_e4 : ensures4 lst target ret1)
    : ensures5 lst target ret1 := by
    exact hpost1.2.2.2.2

theorem uniqueness_3
    (lst : List ℕ)
    (target : ℕ)
    (hpre : precondition lst target)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition lst target ret1)
    (hpost2 : postcondition lst target ret2)
    (h1_e1 : ensures1 lst target ret1)
    (h1_e4 : ensures4 lst target ret1)
    (h1_e5 : ensures5 lst target ret1)
    : ensures1 lst target ret2 := by
    intros; expose_names; exact (uniqueness_0 lst target hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_4
    (lst : List ℕ)
    (target : ℕ)
    (hpre : precondition lst target)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition lst target ret1)
    (hpost2 : postcondition lst target ret2)
    (h1_e1 : ensures1 lst target ret1)
    (h1_e4 : ensures4 lst target ret1)
    (h1_e5 : ensures5 lst target ret1)
    (h2_e1 : ensures1 lst target ret2)
    : ensures4 lst target ret2 := by
    intros; expose_names; exact (uniqueness_1 lst target hpre ret2 ret1 hpost2 hpost1 h2_e1); done

theorem uniqueness_5
    (lst : List ℕ)
    (target : ℕ)
    (hpre : precondition lst target)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition lst target ret1)
    (hpost2 : postcondition lst target ret2)
    (h1_e1 : ensures1 lst target ret1)
    (h1_e4 : ensures4 lst target ret1)
    (h1_e5 : ensures5 lst target ret1)
    (h2_e1 : ensures1 lst target ret2)
    (h2_e4 : ensures4 lst target ret2)
    : ensures5 lst target ret2 := by
    intros; expose_names; exact (uniqueness_2 lst target hpre ret2 ret1 hpost2 hpost1 h2_e1 h2_e4); done

theorem uniqueness_6
    (lst : List ℕ)
    (target : ℕ)
    (hpre : precondition lst target)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition lst target ret1)
    (hpost2 : postcondition lst target ret2)
    (h1_e1 : ensures1 lst target ret1)
    (h1_e4 : ensures4 lst target ret1)
    (h1_e5 : ensures5 lst target ret1)
    (h2_e1 : ensures1 lst target ret2)
    (h2_e4 : ensures4 lst target ret2)
    (h2_e5 : ensures5 lst target ret2)
    (hcount_target_ret1 : List.count target ret1 = 0)
    (hcount_target_ret2 : List.count target ret2 = 0)
    (hcount_neq_ret1 : ∀ (x : ℕ), ¬x = target → List.count x ret1 = List.count x lst)
    (hcount_neq_ret2 : ∀ (x : ℕ), ¬x = target → List.count x ret2 = List.count x lst)
    : ∀ (x : ℕ), List.count x ret1 = List.count x ret2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_7
    (lst : List ℕ)
    (target : ℕ)
    (hpre : precondition lst target)
    (ret1 : List ℕ)
    (ret2 : List ℕ)
    (hpost1 : postcondition lst target ret1)
    (hpost2 : postcondition lst target ret2)
    (h1_e1 : ensures1 lst target ret1)
    (h1_e4 : ensures4 lst target ret1)
    (h1_e5 : ensures5 lst target ret1)
    (h2_e1 : ensures1 lst target ret2)
    (h2_e4 : ensures4 lst target ret2)
    (h2_e5 : ensures5 lst target ret2)
    (hcount_target_ret1 : List.count target ret1 = 0)
    (hcount_target_ret2 : List.count target ret2 = 0)
    (hcount_neq_ret1 : ∀ (x : ℕ), ¬x = target → List.count x ret1 = List.count x lst)
    (hcount_neq_ret2 : ∀ (x : ℕ), ¬x = target → List.count x ret2 = List.count x lst)
    (hcount_eq : ∀ (x : ℕ), List.count x ret1 = List.count x ret2)
    (hperm : ret1.Perm ret2)
    (hsublist1 : ret1.Sublist lst)
    (hsublist2 : ret2.Sublist lst)
    (hlen_eq : ret1.length = ret2.length)
    : ret1.Sublist ret2 := by
    sorry

theorem uniqueness (lst : List Nat) (target : Nat):
  precondition lst target →
  (∀ ret1 ret2,
    postcondition lst target ret1 →
    postcondition lst target ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Extract the postcondition components for ret1
  have h1_e1 : ensures1 lst target ret1 := by (try simp at *; expose_names); exact (uniqueness_0 lst target hpre ret1 ret2 hpost1 hpost2); done
  have h1_e4 : ensures4 lst target ret1 := by (try simp at *; expose_names); exact (uniqueness_1 lst target hpre ret1 ret2 hpost1 hpost2 h1_e1); done
  have h1_e5 : ensures5 lst target ret1 := by (try simp at *; expose_names); exact (uniqueness_2 lst target hpre ret1 ret2 hpost1 hpost2 h1_e1 h1_e4); done
  -- Extract the postcondition components for ret2
  have h2_e1 : ensures1 lst target ret2 := by (try simp at *; expose_names); exact (uniqueness_3 lst target hpre ret1 ret2 hpost1 hpost2 h1_e1 h1_e4 h1_e5); done
  have h2_e4 : ensures4 lst target ret2 := by (try simp at *; expose_names); exact (uniqueness_4 lst target hpre ret1 ret2 hpost1 hpost2 h1_e1 h1_e4 h1_e5 h2_e1); done
  have h2_e5 : ensures5 lst target ret2 := by (try simp at *; expose_names); exact (uniqueness_5 lst target hpre ret1 ret2 hpost1 hpost2 h1_e1 h1_e4 h1_e5 h2_e1 h2_e4); done
  -- From ensures1, target has count 0 in ret1 (target ∉ ret1)
  have hcount_target_ret1 : List.count target ret1 = 0 := by (try simp at *; expose_names); exact (List.count_eq_zero.mpr h1_e1); done
  -- From ensures1, target has count 0 in ret2 (target ∉ ret2)
  have hcount_target_ret2 : List.count target ret2 = 0 := by (try simp at *; expose_names); exact (List.count_eq_zero.mpr h2_e1); done
  -- For x ≠ target, ret1.count x = lst.count x by ensures5
  have hcount_neq_ret1 : ∀ x, x ≠ target → List.count x ret1 = List.count x lst := by (try simp at *; expose_names); exact (fun x a ↦ h1_e5 x a); done
  -- For x ≠ target, ret2.count x = lst.count x by ensures5
  have hcount_neq_ret2 : ∀ x, x ≠ target → List.count x ret2 = List.count x lst := by (try simp at *; expose_names); exact (fun x a ↦ h2_e5 x a); done
  -- For all elements, ret1 and ret2 have the same count
  have hcount_eq : ∀ x, List.count x ret1 = List.count x ret2 := by (try simp at *; expose_names); exact (uniqueness_6 lst target hpre ret1 ret2 hpost1 hpost2 h1_e1 h1_e4 h1_e5 h2_e1 h2_e4 h2_e5 hcount_target_ret1 hcount_target_ret2 hcount_neq_ret1 hcount_neq_ret2); done
  -- Two lists with equal counts for all elements are permutations (List.perm_iff_count)
  have hperm : ret1.Perm ret2 := by (try simp at *; expose_names); exact (List.perm_iff_count.mpr hcount_eq); done
  -- ret1.Sublist lst from ensures4
  have hsublist1 : ret1.Sublist lst := by (try simp at *; expose_names); exact h1_e4; done
  -- ret2.Sublist lst from ensures4
  have hsublist2 : ret2.Sublist lst := by (try simp at *; expose_names); exact h2_e4; done
  -- Permutations have equal length
  have hlen_eq : ret1.length = ret2.length := by (try simp at *; expose_names); exact (List.Perm.length_eq hperm); done
  -- A permutation that is also a sublist of the same parent must be equal
  -- We prove ret2 is a sublist of ret1 ++ [] = ret1 using the permutation
  -- Actually, use Perm.sublist_iff: l₁ ~ l₂ implies (l₁ <+ l ↔ l₂ <+ l)
  -- Since ret1.Perm ret2 and both <+ lst, we use structural argument
  -- Key: use that Perm.eq_of_sorted works for any order, or direct induction
  -- Alternative: show ret1 <+ ret2 from ret1 ~ ret2 and both <+ lst
  have hsublist_ret1_ret2 : ret1.Sublist ret2 := by (try simp at *; expose_names); exact (uniqueness_7 lst target hpre ret1 ret2 hpost1 hpost2 h1_e1 h1_e4 h1_e5 h2_e1 h2_e4 h2_e5 hcount_target_ret1 hcount_target_ret2 hcount_neq_ret1 hcount_neq_ret2 hcount_eq hperm hsublist1 hsublist2 hlen_eq); done
  -- Now use Sublist.eq_of_length
  have heq : ret1 = ret2 := by (try simp at *; expose_names); exact ((List.Sublist.length_eq hsublist_ret1_ret2).mp hlen_eq); done
  exact heq
end Proof
