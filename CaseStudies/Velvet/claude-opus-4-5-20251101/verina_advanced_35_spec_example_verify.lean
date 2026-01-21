import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def isMajority (nums : List Int) (x : Int) : Prop :=
  nums.count x > nums.length / 2



def precondition (nums : List Int) :=
  nums.length ≥ 1 ∧ ∃ x, x ∈ nums ∧ isMajority nums x



def postcondition (nums : List Int) (result : Int) :=
  result ∈ nums ∧ isMajority nums result


def test1_nums : List Int := [3, 2, 3]

def test1_Expected : Int := 3

def test2_nums : List Int := [2, 2, 1, 1, 1, 2, 2]

def test2_Expected : Int := 2

def test5_nums : List Int := [7]

def test5_Expected : Int := 7







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  unfold precondition test1_nums isMajority
  constructor
  · native_decide
  · use 3
    constructor
    · native_decide
    · native_decide

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition test1_nums test1_Expected isMajority
  native_decide

theorem test2_precondition :
  precondition test2_nums := by
  unfold precondition test2_nums isMajority
  constructor
  · native_decide
  · use 2
    constructor
    · native_decide
    · native_decide

theorem test2_postcondition :
  postcondition test2_nums test2_Expected := by
  unfold postcondition test2_nums test2_Expected isMajority
  native_decide

theorem test5_precondition :
  precondition test5_nums := by
  unfold precondition test5_nums isMajority
  constructor
  · native_decide
  · use 7
    constructor
    · native_decide
    · native_decide

theorem test5_postcondition :
  postcondition test5_nums test5_Expected := by
  unfold postcondition test5_nums test5_Expected isMajority
  native_decide

theorem uniqueness_0
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hmem1 : ret1 ∈ nums)
    (hmem2 : ret2 ∈ nums)
    (hne : ¬ret1 = ret2)
    (hmaj1 : nums.length / 2 < List.count ret1 nums)
    (hmaj2 : nums.length / 2 < List.count ret2 nums)
    (hcount1_bound : nums.length / 2 + 1 ≤ List.count ret1 nums)
    (hcount2_bound : nums.length / 2 + 1 ≤ List.count ret2 nums)
    (hsum_bound : nums.length / 2 + 1 + (nums.length / 2 + 1) ≤ List.count ret1 nums + List.count ret2 nums)
    : nums.length < nums.length / 2 + nums.length / 2 + 2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_1
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hmem1 : ret1 ∈ nums)
    (hmem2 : ret2 ∈ nums)
    (hne : ¬ret1 = ret2)
    (hmaj1 : nums.length / 2 < List.count ret1 nums)
    (hmaj2 : nums.length / 2 < List.count ret2 nums)
    (hcount1_bound : nums.length / 2 + 1 ≤ List.count ret1 nums)
    (hcount2_bound : nums.length / 2 + 1 ≤ List.count ret2 nums)
    (hsum_bound : nums.length / 2 + 1 + (nums.length / 2 + 1) ≤ List.count ret1 nums + List.count ret2 nums)
    (hdiv_property : nums.length < nums.length / 2 + nums.length / 2 + 2)
    : nums.length < List.count ret1 nums + List.count ret2 nums := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_2
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hmem1 : ret1 ∈ nums)
    (hmem2 : ret2 ∈ nums)
    (hne : ¬ret1 = ret2)
    (hcount1_le : List.count ret1 nums ≤ nums.length)
    (hcount2_le : List.count ret2 nums ≤ nums.length)
    (hmaj1 : nums.length / 2 < List.count ret1 nums)
    (hmaj2 : nums.length / 2 < List.count ret2 nums)
    (hcount1_bound : nums.length / 2 + 1 ≤ List.count ret1 nums)
    (hcount2_bound : nums.length / 2 + 1 ≤ List.count ret2 nums)
    (hsum_bound : nums.length / 2 + 1 + (nums.length / 2 + 1) ≤ List.count ret1 nums + List.count ret2 nums)
    (hdiv_property : nums.length < nums.length / 2 + nums.length / 2 + 2)
    (hsum_exceeds : nums.length < List.count ret1 nums + List.count ret2 nums)
    : ∀ (l : List ℤ) (a b : ℤ), ¬a = b → List.count a l + List.count b l ≤ l.length := by
    intro l a b hab
    induction l with
    | nil => simp
    | cons x xs ih =>
      rw [List.count_cons, List.count_cons, List.length_cons]
      have ih_used : List.count a xs + List.count b xs ≤ xs.length := ih
      by_cases hxa : x == a <;> by_cases hxb : x == b
      · -- x == a and x == b, contradiction since a ≠ b
        simp only [beq_iff_eq] at hxa hxb
        subst hxa hxb
        exact absurd rfl hab
      · -- x == a and x ≠ b
        simp only [hxa, hxb, ↓reduceIte, add_zero]
        have h1 : (if true = true then 1 else 0) = 1 := rfl
        have h2 : (if false = true then 1 else 0) = 0 := rfl
        simp only [h1, h2] at *
        omega
      · -- x ≠ a and x == b
        simp only [hxa, hxb, ↓reduceIte, add_zero]
        have h1 : (if true = true then 1 else 0) = 1 := rfl
        have h2 : (if false = true then 1 else 0) = 0 := rfl
        simp only [h1, h2] at *
        omega
      · -- x ≠ a and x ≠ b
        simp only [hxa, hxb, ↓reduceIte, add_zero]
        have h2 : (if false = true then 1 else 0) = 0 := rfl
        simp only [h2] at *
        omega

theorem uniqueness (nums : List Int):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  unfold isMajority at hpost1 hpost2
  obtain ⟨hmem1, hmaj1⟩ := hpost1
  obtain ⟨hmem2, hmaj2⟩ := hpost2
  by_contra hne
  have hcount1_bound : nums.count ret1 ≥ nums.length / 2 + 1 := by (try simp at *; expose_names); exact (hmaj1); done
  have hcount2_bound : nums.count ret2 ≥ nums.length / 2 + 1 := by (try simp at *; expose_names); exact (hmaj2); done
  have hsum_bound : nums.count ret1 + nums.count ret2 ≥ nums.length / 2 + 1 + (nums.length / 2 + 1) := by (try simp at *; expose_names); exact (Nat.add_le_add hmaj1 hmaj2); done
  have hdiv_property : nums.length / 2 + nums.length / 2 + 2 > nums.length := by (try simp at *; expose_names); exact (uniqueness_0 nums hpre ret1 ret2 hmem1 hmem2 hne hmaj1 hmaj2 hcount1_bound hcount2_bound hsum_bound); done
  have hsum_exceeds : nums.count ret1 + nums.count ret2 > nums.length := by (try simp at *; expose_names); exact (uniqueness_1 nums hpre ret1 ret2 hmem1 hmem2 hne hmaj1 hmaj2 hcount1_bound hcount2_bound hsum_bound hdiv_property); done
  have hcount1_le : nums.count ret1 ≤ nums.length := by (try simp at *; expose_names); exact (List.count_le_length); done
  have hcount2_le : nums.count ret2 ≤ nums.length := by (try simp at *; expose_names); exact (List.count_le_length); done
  have hdisjoint_counts : ∀ (l : List Int) (a b : Int), a ≠ b → l.count a + l.count b ≤ l.length := by (try simp at *; expose_names); exact (uniqueness_2 nums hpre ret1 ret2 hmem1 hmem2 hne hcount1_le hcount2_le hmaj1 hmaj2 hcount1_bound hcount2_bound hsum_bound hdiv_property hsum_exceeds); done
  have hsum_le_length : nums.count ret1 + nums.count ret2 ≤ nums.length := by (try simp at *; expose_names); exact (hdisjoint_counts nums ret1 ret2 hne); done
  have hcontra : nums.count ret1 + nums.count ret2 > nums.length ∧ nums.count ret1 + nums.count ret2 ≤ nums.length := by (try simp at *; expose_names); exact (⟨hsum_exceeds, hdisjoint_counts nums ret1 ret2 hne⟩); done
  omega
end Proof
