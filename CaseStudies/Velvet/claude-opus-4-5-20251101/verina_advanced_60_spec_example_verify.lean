import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isEven (n : Nat) : Bool := n % 2 = 0


def isOdd (n : Nat) : Bool := n % 2 ≠ 0




def ensures1 (nums : List Nat) (result : List Nat × List Nat) :=
  result.1.Sublist nums ∧ result.2.Sublist nums


def ensures2 (nums : List Nat) (result : List Nat × List Nat) :=
  (∀ x ∈ result.1, x % 2 = 0) ∧ (∀ x ∈ result.2, x % 2 ≠ 0)


def ensures3 (nums : List Nat) (result : List Nat × List Nat) :=
  (∀ x ∈ nums, x % 2 = 0 → x ∈ result.1) ∧
  (∀ x ∈ nums, x % 2 ≠ 0 → x ∈ result.2)


def ensures4 (nums : List Nat) (result : List Nat × List Nat) :=
  (∀ x, x % 2 = 0 → result.1.count x = nums.count x) ∧
  (∀ x, x % 2 ≠ 0 → result.2.count x = nums.count x)

def precondition (nums : List Nat) :=
  nums.Nodup

def postcondition (nums : List Nat) (result : List Nat × List Nat) :=
  ensures1 nums result ∧ ensures2 nums result ∧ ensures3 nums result ∧ ensures4 nums result


def test1_nums : List Nat := [1, 2, 3, 4, 5, 6]

def test1_Expected : List Nat × List Nat := ([2, 4, 6], [1, 3, 5])

def test3_nums : List Nat := []

def test3_Expected : List Nat × List Nat := ([], [])

def test4_nums : List Nat := [2, 4, 6, 8]

def test4_Expected : List Nat × List Nat := ([2, 4, 6, 8], [])







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  unfold precondition test1_nums
  decide

theorem test1_postcondition_0
    (x : ℕ)
    (hmod : x % 2 = 0)
    : ¬x = 2 → ¬x = 4 → ¬x = 6 → List.count x [2, 4, 6] = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_1
    (x : ℕ)
    (hmod : x % 2 = 0)
    (h_not_in_evens : ¬x = 2 → ¬x = 4 → ¬x = 6 → List.count x [2, 4, 6] = 0)
    : ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → ¬x = 5 → ¬x = 6 → List.count x [1, 2, 3, 4, 5, 6] = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_2
    (x : ℕ)
    (hmod : x % 2 = 0)
    (h_not_in_evens : x ∉ [2, 4, 6] → List.count x [2, 4, 6] = 0)
    (h_not_in_nums : x ∉ [1, 2, 3, 4, 5, 6] → List.count x [1, 2, 3, 4, 5, 6] = 0)
    : x ∈ [2, 4, 6] ↔ x = 2 ∨ x = 4 ∨ x = 6 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_3
    (x : ℕ)
    (hmod : x % 2 = 0)
    (h_not_in_evens : x ∉ [2, 4, 6] → List.count x [2, 4, 6] = 0)
    (h_not_in_nums : x ∉ [1, 2, 3, 4, 5, 6] → List.count x [1, 2, 3, 4, 5, 6] = 0)
    (h_in_evens_iff : x ∈ [2, 4, 6] ↔ x = 2 ∨ x = 4 ∨ x = 6)
    : x ∈ [1, 2, 3, 4, 5, 6] ↔ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_4
    (x : ℕ)
    (hmod : x % 2 = 0)
    (h2 : ¬x = 2)
    (h4 : ¬x = 4)
    (h6 : ¬x = 6)
    (h_not_in_evens : ¬x = 2 → ¬x = 4 → ¬x = 6 → List.count x [2, 4, 6] = 0)
    (h_not_in_nums : ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → ¬x = 5 → ¬x = 6 → List.count x [1, 2, 3, 4, 5, 6] = 0)
    (h_in_evens_iff : True)
    (h_in_nums_iff : True)
    : ¬x = 2 ∧ ¬x = 4 ∧ ¬x = 6 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_5
    (x : ℕ)
    (hmod : x % 2 = 0)
    (h2 : ¬x = 2)
    (h4 : ¬x = 4)
    (h6 : ¬x = 6)
    (h_not_in_evens : ¬x = 2 → ¬x = 4 → ¬x = 6 → List.count x [2, 4, 6] = 0)
    (h_not_in_nums : ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → ¬x = 5 → ¬x = 6 → List.count x [1, 2, 3, 4, 5, 6] = 0)
    (h_in_evens_iff : True)
    (h_in_nums_iff : True)
    (hne : ¬x = 2 ∧ ¬x = 4 ∧ ¬x = 6)
    : ¬x = 1 ∧ ¬x = 2 ∧ ¬x = 3 ∧ ¬x = 4 ∧ ¬x = 5 ∧ ¬x = 6 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_6
    (x : ℕ)
    (hmod : x % 2 = 1)
    : ¬x = 1 → ¬x = 3 → ¬x = 5 → List.count x [1, 3, 5] = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_7
    (x : ℕ)
    (hmod : x % 2 = 1)
    (h_not_in_odds : ¬x = 1 → ¬x = 3 → ¬x = 5 → List.count x [1, 3, 5] = 0)
    : ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → ¬x = 5 → ¬x = 6 → List.count x [1, 2, 3, 4, 5, 6] = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_8
    (x : ℕ)
    (hmod : x % 2 ≠ 0)
    (h_not_in_odds : x ∉ [1, 3, 5] → List.count x [1, 3, 5] = 0)
    (h_not_in_nums : x ∉ [1, 2, 3, 4, 5, 6] → List.count x [1, 2, 3, 4, 5, 6] = 0)
    : x ∈ [1, 3, 5] ↔ x = 1 ∨ x = 3 ∨ x = 5 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_9
    (x : ℕ)
    (hmod : x % 2 ≠ 0)
    (h_not_in_odds : x ∉ [1, 3, 5] → List.count x [1, 3, 5] = 0)
    (h_not_in_nums : x ∉ [1, 2, 3, 4, 5, 6] → List.count x [1, 2, 3, 4, 5, 6] = 0)
    (h_in_odds_iff : x ∈ [1, 3, 5] ↔ x = 1 ∨ x = 3 ∨ x = 5)
    : x ∈ [1, 2, 3, 4, 5, 6] ↔ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_10
    (x : ℕ)
    (h1 : ¬x = 1)
    (h3 : ¬x = 3)
    (h5 : ¬x = 5)
    (hmod : x % 2 = 1)
    (h_not_in_odds : ¬x = 1 → ¬x = 3 → ¬x = 5 → List.count x [1, 3, 5] = 0)
    (h_not_in_nums : ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → ¬x = 5 → ¬x = 6 → List.count x [1, 2, 3, 4, 5, 6] = 0)
    (h_in_odds_iff : True)
    (h_in_nums_iff : True)
    : ¬x = 1 ∧ ¬x = 3 ∧ ¬x = 5 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_11
    (x : ℕ)
    (h1 : ¬x = 1)
    (h3 : ¬x = 3)
    (h5 : ¬x = 5)
    (hmod : x % 2 = 1)
    (h_not_in_odds : ¬x = 1 → ¬x = 3 → ¬x = 5 → List.count x [1, 3, 5] = 0)
    (h_not_in_nums : ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → ¬x = 5 → ¬x = 6 → List.count x [1, 2, 3, 4, 5, 6] = 0)
    (h_in_odds_iff : True)
    (h_in_nums_iff : True)
    (hne : ¬x = 1 ∧ ¬x = 3 ∧ ¬x = 5)
    : ¬x = 1 ∧ ¬x = 2 ∧ ¬x = 3 ∧ ¬x = 4 ∧ ¬x = 5 ∧ ¬x = 6 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 test1_nums test1_Expected
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- [2, 4, 6].Sublist [1, 2, 3, 4, 5, 6]
    decide
  · -- [1, 3, 5].Sublist [1, 2, 3, 4, 5, 6]
    decide
  · -- ∀ x ∈ [2, 4, 6], x % 2 = 0
    intro x hx
    fin_cases hx <;> native_decide
  · -- ∀ x ∈ [1, 3, 5], x % 2 ≠ 0
    intro x hx
    fin_cases hx <;> native_decide
  · -- ∀ x ∈ [1, 2, 3, 4, 5, 6], x % 2 = 0 → x ∈ [2, 4, 6]
    intro x hx hmod
    fin_cases hx <;> simp_all
  · -- ∀ x ∈ [1, 2, 3, 4, 5, 6], x % 2 ≠ 0 → x ∈ [1, 3, 5]
    intro x hx hmod
    fin_cases hx <;> simp_all
  · -- ∀ x, x % 2 = 0 → count x [2, 4, 6] = count x [1, 2, 3, 4, 5, 6]
    intro x hmod
    have h_not_in_evens : x ∉ [2, 4, 6] → List.count x [2, 4, 6] = 0 := by (try simp at *; expose_names); exact (test1_postcondition_0 x hmod); done
    have h_not_in_nums : x ∉ [1, 2, 3, 4, 5, 6] → List.count x [1, 2, 3, 4, 5, 6] = 0 := by (try simp at *; expose_names); exact (test1_postcondition_1 x hmod h_not_in_evens); done
    have h_in_evens_iff : x ∈ [2, 4, 6] ↔ x = 2 ∨ x = 4 ∨ x = 6 := by (try simp at *; expose_names); exact (test1_postcondition_2 x hmod h_not_in_evens h_not_in_nums); done
    have h_in_nums_iff : x ∈ [1, 2, 3, 4, 5, 6] ↔ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by (try simp at *; expose_names); exact (test1_postcondition_3 x hmod h_not_in_evens h_not_in_nums h_in_evens_iff); done
    by_cases h2 : x = 2
    · subst h2; native_decide
    · by_cases h4 : x = 4
      · subst h4; native_decide
      · by_cases h6 : x = 6
        · subst h6; native_decide
        · have hne : x ∉ [2, 4, 6] := by (try simp at *; expose_names); exact (test1_postcondition_4 x hmod h2 h4 h6 h_not_in_evens h_not_in_nums h_in_evens_iff h_in_nums_iff); done
          have hne2 : x ∉ [1, 2, 3, 4, 5, 6] := by (try simp at *; expose_names); exact (test1_postcondition_5 x hmod h2 h4 h6 h_not_in_evens h_not_in_nums h_in_evens_iff h_in_nums_iff hne); done
          simp only [h_not_in_evens hne, h_not_in_nums hne2]
  · -- ∀ x, x % 2 ≠ 0 → count x [1, 3, 5] = count x [1, 2, 3, 4, 5, 6]
    intro x hmod
    have h_not_in_odds : x ∉ [1, 3, 5] → List.count x [1, 3, 5] = 0 := by (try simp at *; expose_names); exact (test1_postcondition_6 x hmod); done
    have h_not_in_nums : x ∉ [1, 2, 3, 4, 5, 6] → List.count x [1, 2, 3, 4, 5, 6] = 0 := by (try simp at *; expose_names); exact (test1_postcondition_7 x hmod h_not_in_odds); done
    have h_in_odds_iff : x ∈ [1, 3, 5] ↔ x = 1 ∨ x = 3 ∨ x = 5 := by (try simp at *; expose_names); exact (test1_postcondition_8 x hmod h_not_in_odds h_not_in_nums); done
    have h_in_nums_iff : x ∈ [1, 2, 3, 4, 5, 6] ↔ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by (try simp at *; expose_names); exact (test1_postcondition_9 x hmod h_not_in_odds h_not_in_nums h_in_odds_iff); done
    by_cases h1 : x = 1
    · subst h1; native_decide
    · by_cases h3 : x = 3
      · subst h3; native_decide
      · by_cases h5 : x = 5
        · subst h5; native_decide
        · have hne : x ∉ [1, 3, 5] := by (try simp at *; expose_names); exact (test1_postcondition_10 x h1 h3 h5 hmod h_not_in_odds h_not_in_nums h_in_odds_iff h_in_nums_iff); done
          have hne2 : x ∉ [1, 2, 3, 4, 5, 6] := by (try simp at *; expose_names); exact (test1_postcondition_11 x h1 h3 h5 hmod h_not_in_odds h_not_in_nums h_in_odds_iff h_in_nums_iff hne); done
          simp only [h_not_in_odds hne, h_not_in_nums hne2]

theorem test3_precondition :
  precondition test3_nums := by
  unfold precondition test3_nums
  exact List.nodup_nil

theorem test3_postcondition :
  postcondition test3_nums test3_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 test3_nums test3_Expected
  simp only [List.Sublist.slnil, List.not_mem_nil, List.count_nil, and_self, 
             forall_const, implies_true, not_false_eq_true]
  constructor
  · trivial
  constructor
  · constructor <;> intro x hx <;> exact False.elim hx
  constructor
  · constructor <;> intro x hx <;> exact False.elim hx
  · trivial

theorem test4_precondition :
  precondition test4_nums := by
  unfold precondition test4_nums
  decide

theorem test4_postcondition :
  postcondition test4_nums test4_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 test4_nums test4_Expected
  simp only [List.Sublist.refl, List.nil_sublist, true_and]
  constructor
  · constructor
    · intro x hx
      fin_cases hx <;> native_decide
    · intro x hx
      simp only [List.mem_nil_iff] at hx
  · constructor
    · constructor
      · intro x hx hmod
        exact hx
      · intro x hx hmod
        fin_cases hx <;> simp_all
    · constructor
      · intro x hmod
        trivial
      · intro x hmod
        simp only [List.count_nil]
        have h : x ∉ [2, 4, 6, 8] := by
          intro hmem
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl | rfl | rfl <;> omega
        rw [List.count_eq_zero.mpr h]

theorem uniqueness_0
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    : ensures1 nums ret1 := by
    exact hpost1.1

theorem uniqueness_1
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    : ensures2 nums ret1 := by
    exact hpost1.2.1

theorem uniqueness_2
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    : ensures3 nums ret1 := by
    exact hpost1.2.2.1

theorem uniqueness_3
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    : ensures4 nums ret1 := by
    exact hpost1.2.2.2

theorem uniqueness_4
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    : ensures1 nums ret2 := by
    intros; expose_names; exact (uniqueness_0 nums hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_5
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    : ensures2 nums ret2 := by
    intros; expose_names; exact (uniqueness_1 nums hpre ret2 ret1 hpost2 hpost1 h2_ensures1); done

theorem uniqueness_6
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    : ensures3 nums ret2 := by
    intros; expose_names; exact (uniqueness_2 nums hpre ret2 ret1 hpost2 hpost1 h2_ensures1 h2_ensures2); done

theorem uniqueness_7
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    : ensures4 nums ret2 := by
    intros; expose_names; exact (uniqueness_3 nums hpre ret2 ret1 hpost2 hpost1 h2_ensures1 h2_ensures2 h2_ensures3); done

theorem uniqueness_8
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    : ret1.1.Sublist nums := by
    exact h1_ensures1.1

theorem uniqueness_9
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    : ret2.1.Sublist nums := by
    intros; expose_names; exact (uniqueness_8 nums hpre ret2 ret1 hpost2 hpost1 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4); done

theorem uniqueness_10
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    (h2_sub1 : ret2.1.Sublist nums)
    : ret1.2.Sublist nums := by
    exact h1_ensures1.2

theorem uniqueness_11
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    (h2_sub1 : ret2.1.Sublist nums)
    (h1_sub2 : ret1.2.Sublist nums)
    : ret2.2.Sublist nums := by
    exact h2_ensures1.2

theorem uniqueness_12
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    (h2_sub1 : ret2.1.Sublist nums)
    (h1_sub2 : ret1.2.Sublist nums)
    (h2_sub2 : ret2.2.Sublist nums)
    (hnodup : nums.Nodup)
    (h1_nodup1 : ret1.1.Nodup)
    (h2_nodup1 : ret2.1.Nodup)
    (h1_nodup2 : ret1.2.Nodup)
    (h2_nodup2 : ret2.2.Nodup)
    : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.1 = List.count x ret2.1 := by
  intro x hmod
  unfold ensures4 at h1_ensures4 h2_ensures4
  have h1 := h1_ensures4.1 x hmod
  have h2 := h2_ensures4.1 x hmod
  omega

theorem uniqueness_13
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    (h2_sub1 : ret2.1.Sublist nums)
    (h1_sub2 : ret1.2.Sublist nums)
    (h2_sub2 : ret2.2.Sublist nums)
    (hnodup : nums.Nodup)
    (h1_nodup1 : ret1.1.Nodup)
    (h2_nodup1 : ret2.1.Nodup)
    (h1_nodup2 : ret1.2.Nodup)
    (h2_nodup2 : ret2.2.Nodup)
    (hcount_even : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.1 = List.count x ret2.1)
    : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.1 = 0 := by
    intro x hx_odd
    -- h1_ensures2 tells us all elements in ret1.1 are even
    unfold ensures2 at h1_ensures2
    have h_all_even : ∀ y ∈ ret1.1, y % 2 = 0 := h1_ensures2.1
    -- If x % 2 = 1, then x % 2 ≠ 0
    have hx_not_even : x % 2 ≠ 0 := by omega
    -- Therefore x is not in ret1.1
    have hx_not_mem : x ∉ ret1.1 := by
      intro hx_mem
      have := h_all_even x hx_mem
      omega
    -- Count of element not in list is 0
    exact List.count_eq_zero_of_not_mem hx_not_mem

theorem uniqueness_14
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    (h2_sub1 : ret2.1.Sublist nums)
    (h1_sub2 : ret1.2.Sublist nums)
    (h2_sub2 : ret2.2.Sublist nums)
    (hnodup : nums.Nodup)
    (h1_nodup1 : ret1.1.Nodup)
    (h2_nodup1 : ret2.1.Nodup)
    (h1_nodup2 : ret1.2.Nodup)
    (h2_nodup2 : ret2.2.Nodup)
    (hcount_even : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.1 = List.count x ret2.1)
    (hcount_odd_in_evens1 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.1 = 0)
    : ∀ (x : ℕ), x % 2 = 1 → List.count x ret2.1 = 0 := by
  intro x hx_odd
  -- From h2_ensures2, we know all elements in ret2.1 are even
  unfold ensures2 at h2_ensures2
  obtain ⟨h_evens, _⟩ := h2_ensures2
  -- Show x ∉ ret2.1 because x is odd but all elements in ret2.1 are even
  have hx_not_mem : x ∉ ret2.1 := by
    intro hx_in
    have hx_even := h_evens x hx_in
    omega
  exact List.count_eq_zero_of_not_mem hx_not_mem

theorem uniqueness_15
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    (h2_sub1 : ret2.1.Sublist nums)
    (h1_sub2 : ret1.2.Sublist nums)
    (h2_sub2 : ret2.2.Sublist nums)
    (hnodup : nums.Nodup)
    (h1_nodup1 : ret1.1.Nodup)
    (h2_nodup1 : ret2.1.Nodup)
    (h1_nodup2 : ret1.2.Nodup)
    (h2_nodup2 : ret2.2.Nodup)
    (hcount_even : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.1 = List.count x ret2.1)
    (hcount_odd_in_evens1 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.1 = 0)
    (hcount_odd_in_evens2 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret2.1 = 0)
    : ∀ (x : ℕ), List.count x ret1.1 = List.count x ret2.1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_16
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    (h2_sub1 : ret2.1.Sublist nums)
    (h1_sub2 : ret1.2.Sublist nums)
    (h2_sub2 : ret2.2.Sublist nums)
    (hnodup : nums.Nodup)
    (h1_nodup1 : ret1.1.Nodup)
    (h2_nodup1 : ret2.1.Nodup)
    (h1_nodup2 : ret1.2.Nodup)
    (h2_nodup2 : ret2.2.Nodup)
    (hcount_even : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.1 = List.count x ret2.1)
    (hcount_eq1 : ∀ (x : ℕ), List.count x ret1.1 = List.count x ret2.1)
    (hcount_odd_in_evens1 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.1 = 0)
    (hcount_odd_in_evens2 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret2.1 = 0)
    : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.2 = List.count x ret2.2 := by
  intro x hx
  -- x % 2 = 1 implies x % 2 ≠ 0
  have hne : x % 2 ≠ 0 := by omega
  -- From ensures4 definition, extract the second component for both ret1 and ret2
  unfold ensures4 at h1_ensures4 h2_ensures4
  -- h1_ensures4.2 : ∀ x, x % 2 ≠ 0 → ret1.2.count x = nums.count x
  -- h2_ensures4.2 : ∀ x, x % 2 ≠ 0 → ret2.2.count x = nums.count x
  have h1 : List.count x ret1.2 = List.count x nums := h1_ensures4.2 x hne
  have h2 : List.count x ret2.2 = List.count x nums := h2_ensures4.2 x hne
  -- By transitivity
  rw [h1, h2]

theorem uniqueness_17
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    (h2_sub1 : ret2.1.Sublist nums)
    (h1_sub2 : ret1.2.Sublist nums)
    (h2_sub2 : ret2.2.Sublist nums)
    (hnodup : nums.Nodup)
    (h1_nodup1 : ret1.1.Nodup)
    (h2_nodup1 : ret2.1.Nodup)
    (h1_nodup2 : ret1.2.Nodup)
    (h2_nodup2 : ret2.2.Nodup)
    (hcount_even : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.1 = List.count x ret2.1)
    (hcount_eq1 : ∀ (x : ℕ), List.count x ret1.1 = List.count x ret2.1)
    (hcount_odd_in_evens1 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.1 = 0)
    (hcount_odd_in_evens2 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret2.1 = 0)
    (hcount_odd : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.2 = List.count x ret2.2)
    : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.2 = 0 := by
    intro x heven
    -- From h1_ensures2, all elements in ret1.2 are odd
    unfold ensures2 at h1_ensures2
    have hodd_in_ret12 : ∀ y ∈ ret1.2, y % 2 ≠ 0 := h1_ensures2.2
    -- Show x is not in ret1.2
    have hx_not_in : x ∉ ret1.2 := by
      intro hmem
      have hcontra := hodd_in_ret12 x hmem
      exact hcontra heven
    -- Apply the lemma that count equals zero if not a member
    exact List.count_eq_zero_of_not_mem hx_not_in

theorem uniqueness_18
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    (h2_sub1 : ret2.1.Sublist nums)
    (h1_sub2 : ret1.2.Sublist nums)
    (h2_sub2 : ret2.2.Sublist nums)
    (hnodup : nums.Nodup)
    (h1_nodup1 : ret1.1.Nodup)
    (h2_nodup1 : ret2.1.Nodup)
    (h1_nodup2 : ret1.2.Nodup)
    (h2_nodup2 : ret2.2.Nodup)
    (hcount_even : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.1 = List.count x ret2.1)
    (hcount_eq1 : ∀ (x : ℕ), List.count x ret1.1 = List.count x ret2.1)
    (hcount_even_in_odds1 : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.2 = 0)
    (hcount_odd_in_evens1 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.1 = 0)
    (hcount_odd_in_evens2 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret2.1 = 0)
    (hcount_odd : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.2 = List.count x ret2.2)
    : ∀ (x : ℕ), x % 2 = 0 → List.count x ret2.2 = 0 := by
  intro x hx
  apply List.count_eq_zero_of_not_mem
  intro hmem
  unfold ensures2 at h2_ensures2
  have h_odd := h2_ensures2.2 x hmem
  omega

theorem uniqueness_19
    (nums : List ℕ)
    (hpre : precondition nums)
    (ret1 : List ℕ × List ℕ)
    (ret2 : List ℕ × List ℕ)
    (hpost1 : postcondition nums ret1)
    (hpost2 : postcondition nums ret2)
    (h1_ensures1 : ensures1 nums ret1)
    (h1_ensures2 : ensures2 nums ret1)
    (h1_ensures3 : ensures3 nums ret1)
    (h1_ensures4 : ensures4 nums ret1)
    (h2_ensures1 : ensures1 nums ret2)
    (h2_ensures2 : ensures2 nums ret2)
    (h2_ensures3 : ensures3 nums ret2)
    (h2_ensures4 : ensures4 nums ret2)
    (h1_sub1 : ret1.1.Sublist nums)
    (h2_sub1 : ret2.1.Sublist nums)
    (h1_sub2 : ret1.2.Sublist nums)
    (h2_sub2 : ret2.2.Sublist nums)
    (hnodup : nums.Nodup)
    (h1_nodup1 : ret1.1.Nodup)
    (h2_nodup1 : ret2.1.Nodup)
    (h1_nodup2 : ret1.2.Nodup)
    (h2_nodup2 : ret2.2.Nodup)
    (hcount_even : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.1 = List.count x ret2.1)
    (hcount_eq1 : ∀ (x : ℕ), List.count x ret1.1 = List.count x ret2.1)
    (hcount_even_in_odds1 : ∀ (x : ℕ), x % 2 = 0 → List.count x ret1.2 = 0)
    (hcount_even_in_odds2 : ∀ (x : ℕ), x % 2 = 0 → List.count x ret2.2 = 0)
    (hcount_odd_in_evens1 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.1 = 0)
    (hcount_odd_in_evens2 : ∀ (x : ℕ), x % 2 = 1 → List.count x ret2.1 = 0)
    (hcount_odd : ∀ (x : ℕ), x % 2 = 1 → List.count x ret1.2 = List.count x ret2.2)
    : ∀ (x : ℕ), List.count x ret1.2 = List.count x ret2.2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (nums : List Nat):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Unfold the postcondition to access its components
  have h1_ensures1 : ensures1 nums ret1 := by (try simp at *; expose_names); exact (uniqueness_0 nums hpre ret1 ret2 hpost1 hpost2); done
  have h1_ensures2 : ensures2 nums ret1 := by (try simp at *; expose_names); exact (uniqueness_1 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1); done
  have h1_ensures3 : ensures3 nums ret1 := by (try simp at *; expose_names); exact (uniqueness_2 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2); done
  have h1_ensures4 : ensures4 nums ret1 := by (try simp at *; expose_names); exact (uniqueness_3 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3); done
  have h2_ensures1 : ensures1 nums ret2 := by (try simp at *; expose_names); exact (uniqueness_4 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4); done
  have h2_ensures2 : ensures2 nums ret2 := by (try simp at *; expose_names); exact (uniqueness_5 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1); done
  have h2_ensures3 : ensures3 nums ret2 := by (try simp at *; expose_names); exact (uniqueness_6 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2); done
  have h2_ensures4 : ensures4 nums ret2 := by (try simp at *; expose_names); exact (uniqueness_7 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3); done
  -- ret1.1 and ret2.1 are sublists of nums
  have h1_sub1 : ret1.1.Sublist nums := by (try simp at *; expose_names); exact (uniqueness_8 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4); done
  have h2_sub1 : ret2.1.Sublist nums := by (try simp at *; expose_names); exact (uniqueness_9 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1); done
  -- ret1.2 and ret2.2 are sublists of nums
  have h1_sub2 : ret1.2.Sublist nums := by (try simp at *; expose_names); exact (uniqueness_10 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1 h2_sub1); done
  have h2_sub2 : ret2.2.Sublist nums := by (try simp at *; expose_names); exact (uniqueness_11 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1 h2_sub1 h1_sub2); done
  -- nums has no duplicates (from precondition)
  have hnodup : nums.Nodup := by (try simp at *; expose_names); exact hpre; done
  -- Sublists of nodup lists are nodup
  have h1_nodup1 : ret1.1.Nodup := by (try simp at *; expose_names); exact (List.Sublist.nodup h1_sub1 hpre); done
  have h2_nodup1 : ret2.1.Nodup := by (try simp at *; expose_names); exact (List.Sublist.nodup h2_sub1 hpre); done
  have h1_nodup2 : ret1.2.Nodup := by (try simp at *; expose_names); exact (List.Sublist.nodup h1_sub2 hpre); done
  have h2_nodup2 : ret2.2.Nodup := by (try simp at *; expose_names); exact (List.Sublist.nodup h2_sub2 hpre); done
  -- For even x, counts in ret1.1 and ret2.1 are equal (both equal to nums.count x)
  have hcount_even : ∀ x, x % 2 = 0 → ret1.1.count x = ret2.1.count x := by (try simp at *; expose_names); exact (uniqueness_12 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1 h2_sub1 h1_sub2 h2_sub2 hnodup h1_nodup1 h2_nodup1 h1_nodup2 h2_nodup2); done
  -- For odd x, count in ret1.1 is 0 (since ret1.1 contains only evens)
  have hcount_odd_in_evens1 : ∀ x, x % 2 ≠ 0 → ret1.1.count x = 0 := by (try simp at *; expose_names); exact (uniqueness_13 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1 h2_sub1 h1_sub2 h2_sub2 hnodup h1_nodup1 h2_nodup1 h1_nodup2 h2_nodup2 hcount_even); done
  have hcount_odd_in_evens2 : ∀ x, x % 2 ≠ 0 → ret2.1.count x = 0 := by (try simp at *; expose_names); exact (uniqueness_14 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1 h2_sub1 h1_sub2 h2_sub2 hnodup h1_nodup1 h2_nodup1 h1_nodup2 h2_nodup2 hcount_even hcount_odd_in_evens1); done
  -- For all x, counts in ret1.1 and ret2.1 are equal
  have hcount_eq1 : ∀ x, ret1.1.count x = ret2.1.count x := by (try simp at *; expose_names); exact (uniqueness_15 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1 h2_sub1 h1_sub2 h2_sub2 hnodup h1_nodup1 h2_nodup1 h1_nodup2 h2_nodup2 hcount_even hcount_odd_in_evens1 hcount_odd_in_evens2); done
  -- Similarly for odd parts
  have hcount_odd : ∀ x, x % 2 ≠ 0 → ret1.2.count x = ret2.2.count x := by (try simp at *; expose_names); exact (uniqueness_16 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1 h2_sub1 h1_sub2 h2_sub2 hnodup h1_nodup1 h2_nodup1 h1_nodup2 h2_nodup2 hcount_even hcount_eq1 hcount_odd_in_evens1 hcount_odd_in_evens2); done
  have hcount_even_in_odds1 : ∀ x, x % 2 = 0 → ret1.2.count x = 0 := by (try simp at *; expose_names); exact (uniqueness_17 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1 h2_sub1 h1_sub2 h2_sub2 hnodup h1_nodup1 h2_nodup1 h1_nodup2 h2_nodup2 hcount_even hcount_eq1 hcount_odd_in_evens1 hcount_odd_in_evens2 hcount_odd); done
  have hcount_even_in_odds2 : ∀ x, x % 2 = 0 → ret2.2.count x = 0 := by (try simp at *; expose_names); exact (uniqueness_18 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1 h2_sub1 h1_sub2 h2_sub2 hnodup h1_nodup1 h2_nodup1 h1_nodup2 h2_nodup2 hcount_even hcount_eq1 hcount_even_in_odds1 hcount_odd_in_evens1 hcount_odd_in_evens2 hcount_odd); done
  have hcount_eq2 : ∀ x, ret1.2.count x = ret2.2.count x := by (try simp at *; expose_names); exact (uniqueness_19 nums hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h1_ensures4 h2_ensures1 h2_ensures2 h2_ensures3 h2_ensures4 h1_sub1 h2_sub1 h1_sub2 h2_sub2 hnodup h1_nodup1 h2_nodup1 h1_nodup2 h2_nodup2 hcount_even hcount_eq1 hcount_even_in_odds1 hcount_even_in_odds2 hcount_odd_in_evens1 hcount_odd_in_evens2 hcount_odd); done
  -- Equal counts implies permutation
  have hperm1 : ret1.1.Perm ret2.1 := by (try simp at *; expose_names); exact (List.perm_iff_count.mpr hcount_eq1); done
  have hperm2 : ret1.2.Perm ret2.2 := by (try simp at *; expose_names); exact (List.perm_iff_count.mpr hcount_eq2); done
  -- Two sublists of a nodup list that are permutations must be equal
  have heq1 : ret1.1 = ret2.1 := by (try simp at *; expose_names); exact ((List.Nodup.perm_iff_eq_of_sublist hpre h1_sub1 h2_sub1).mp hperm1); done
  have heq2 : ret1.2 = ret2.2 := by (try simp at *; expose_names); exact ((List.Nodup.perm_iff_eq_of_sublist hpre h1_sub2 h2_sub2).mp hperm2); done
  -- Combine to get ret1 = ret2
  exact Prod.ext heq1 heq2
end Proof
