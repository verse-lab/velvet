import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def hasValidSingleNumberProperty (nums : List Int) : Prop :=
  nums.length > 0 ∧
  (∃! x, x ∈ nums ∧ nums.count x = 1) ∧
  (∀ x, x ∈ nums → nums.count x = 1 ∨ nums.count x = 2)


def isSingleNumber (nums : List Int) (result : Int) : Prop :=
  result ∈ nums ∧ nums.count result = 1



def precondition (nums : List Int) :=
  hasValidSingleNumberProperty nums



def postcondition (nums : List Int) (result : Int) :=
  isSingleNumber nums result


def test1_nums : List Int := [2, 2, 3]

def test1_Expected : Int := 3

def test3_nums : List Int := [3, 3, 4, 4, 1]

def test3_Expected : Int := 1

def test6_nums : List Int := [42]

def test6_Expected : Int := 42







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  unfold precondition hasValidSingleNumberProperty test1_nums
  refine ⟨?_, ?_, ?_⟩
  · -- nums.length > 0
    native_decide
  · -- ∃! x, x ∈ nums ∧ nums.count x = 1
    use 3
    constructor
    · -- 3 ∈ [2, 2, 3] ∧ count 3 = 1
      constructor
      · native_decide
      · native_decide
    · -- uniqueness: any y with y ∈ nums ∧ count y = 1 must be 3
      intro y ⟨hy_mem, hy_count⟩
      have h2 : [2, 2, 3].count (2 : Int) = 2 := by native_decide
      have h3 : [2, 2, 3].count (3 : Int) = 1 := by native_decide
      have hmem : y = 2 ∨ y = 3 := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy_mem
        rcases hy_mem with rfl | rfl | rfl
        · left; rfl
        · left; rfl
        · right; rfl
      rcases hmem with rfl | rfl
      · -- y = 2: count 2 = 2 ≠ 1, contradiction
        rw [h2] at hy_count
        contradiction
      · -- y = 3
        rfl
  · -- ∀ x, x ∈ nums → count x = 1 ∨ count x = 2
    intro x hx
    have h2 : [2, 2, 3].count (2 : Int) = 2 := by native_decide
    have h3 : [2, 2, 3].count (3 : Int) = 1 := by native_decide
    have hmem : x = 2 ∨ x = 3 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · left; rfl
      · left; rfl
      · right; rfl
    rcases hmem with rfl | rfl
    · -- x = 2
      right
      exact h2
    · -- x = 3
      left
      exact h3

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition isSingleNumber test1_nums test1_Expected
  native_decide

theorem test3_precondition :
  precondition test3_nums := by
  unfold precondition hasValidSingleNumberProperty test3_nums
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · use 1
    constructor
    · constructor
      · native_decide
      · native_decide
    · intro y ⟨hy_mem, hy_count⟩
      have : y = 3 ∨ y = 4 ∨ y = 1 := by
        simp only [List.mem_cons] at hy_mem
        rcases hy_mem with rfl | rfl | rfl | rfl | rfl | h
        · left; rfl
        · left; rfl
        · right; left; rfl
        · right; left; rfl
        · right; right; rfl
        · simp at h
      rcases this with rfl | rfl | rfl
      · have h2 : List.count 3 [3, 3, 4, 4, 1] = 2 := by native_decide
        have h3 : List.count 3 [3, 3, 4, 4, 1] ≠ 1 := by omega
        exact absurd hy_count h3
      · have h2 : List.count 4 [3, 3, 4, 4, 1] = 2 := by native_decide
        have h3 : List.count 4 [3, 3, 4, 4, 1] ≠ 1 := by omega
        exact absurd hy_count h3
      · rfl
  · intro x hx
    have : x = 3 ∨ x = 4 ∨ x = 1 := by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | h
      · left; rfl
      · left; rfl
      · right; left; rfl
      · right; left; rfl
      · right; right; rfl
      · simp at h
    rcases this with rfl | rfl | rfl
    · right; native_decide
    · right; native_decide
    · left; native_decide

theorem test3_postcondition :
  postcondition test3_nums test3_Expected := by
  unfold postcondition isSingleNumber test3_nums test3_Expected
  native_decide

theorem test6_precondition :
  precondition test6_nums := by
  unfold precondition hasValidSingleNumberProperty test6_nums
  refine ⟨?_, ?_, ?_⟩
  · -- [42].length > 0
    native_decide
  · -- ∃! x, x ∈ [42] ∧ [42].count x = 1
    use 42
    constructor
    · -- 42 ∈ [42] ∧ [42].count 42 = 1
      constructor
      · simp [List.mem_singleton]
      · native_decide
    · -- uniqueness: ∀ y, y ∈ [42] ∧ [42].count y = 1 → y = 42
      intro y ⟨hy_mem, _⟩
      simp [List.mem_singleton] at hy_mem
      exact hy_mem
  · -- ∀ x, x ∈ [42] → [42].count x = 1 ∨ [42].count x = 2
    intro x hx
    simp [List.mem_singleton] at hx
    left
    subst hx
    native_decide

theorem test6_postcondition :
  postcondition test6_nums test6_Expected := by
  unfold postcondition isSingleNumber test6_nums test6_Expected
  native_decide

theorem uniqueness (nums : List Int):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro hpre
  intro ret1 ret2 hpost1 hpost2
  unfold precondition at hpre
  unfold hasValidSingleNumberProperty at hpre
  unfold postcondition at hpost1 hpost2
  unfold isSingleNumber at hpost1 hpost2
  obtain ⟨_, hunique, _⟩ := hpre
  obtain ⟨hret1_mem, hret1_count⟩ := hpost1
  obtain ⟨hret2_mem, hret2_count⟩ := hpost2
  exact ExistsUnique.unique hunique ⟨hret1_mem, hret1_count⟩ ⟨hret2_mem, hret2_count⟩
end Proof
