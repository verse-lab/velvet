import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def countFreq (x : Int) (nums : List Int) : Nat :=
  nums.count x


def distinctElements (nums : List Int) : List Int :=
  nums.eraseDups


def isSortedByFreqDesc (result : List Int) (nums : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < result.length →
    countFreq result[i]! nums ≥ countFreq result[j]! nums



def precondition (nums : List Int) (k : Nat) : Prop :=
  k ≤ (distinctElements nums).length



def ensures1 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  result.length = k


def ensures2 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ∀ x ∈ result, x ∈ nums


def ensures3 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  result.Nodup


def ensures4 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  isSortedByFreqDesc result nums


def ensures5 (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ∀ x ∈ nums, x ∉ result →
    ∀ y ∈ result, countFreq x nums ≤ countFreq y nums

def postcondition (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ensures1 nums k result ∧
  ensures2 nums k result ∧
  ensures3 nums k result ∧
  ensures4 nums k result ∧
  ensures5 nums k result


def test1_nums : List Int := [1, 1, 1, 2, 2, 3]

def test1_k : Nat := 2

def test1_Expected : List Int := [1, 2]

def test2_nums : List Int := [4, 1, -1, 2, -1, 2, 3]

def test2_k : Nat := 2

def test2_Expected : List Int := [-1, 2]

def test3_nums : List Int := [5]

def test3_k : Nat := 1

def test3_Expected : List Int := [5]







section Proof
theorem test1_precondition :
  precondition test1_nums test1_k := by
  simp [precondition, distinctElements, test1_nums, test1_k, List.eraseDups]
  decide

theorem test1_postcondition :
  postcondition test1_nums test1_k test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 ensures5
  unfold isSortedByFreqDesc countFreq
  unfold test1_nums test1_k test1_Expected
  constructor
  · -- ensures1: result.length = k
    native_decide
  constructor
  · -- ensures2: ∀ x ∈ result, x ∈ nums
    intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp [List.mem_cons]
    · simp [List.mem_cons]
  constructor
  · -- ensures3: result.Nodup
    decide
  constructor
  · -- ensures4: isSortedByFreqDesc result nums
    intro i j hij hjlen
    simp only [List.length_cons, List.length_nil] at hjlen
    -- j < 2 and i < j, so (i,j) ∈ {(0,1)}
    match j with
    | 0 => omega
    | 1 => 
      match i with
      | 0 => native_decide
    | n + 2 => omega
  · -- ensures5: ∀ x ∈ nums, x ∉ result → ∀ y ∈ result, countFreq x nums ≤ countFreq y nums
    intro x hx hxnr y hy
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx hy hxnr
    -- x is in nums but not in result, so x = 3
    -- y is in result, so y = 1 or y = 2
    have hx_is_3 : x = 3 := by
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd (Or.inl rfl) hxnr
      · exact absurd (Or.inl rfl) hxnr
      · exact absurd (Or.inl rfl) hxnr
      · exact absurd (Or.inr rfl) hxnr
      · exact absurd (Or.inr rfl) hxnr
      · rfl
    subst hx_is_3
    rcases hy with rfl | rfl
    · native_decide
    · native_decide

theorem test2_precondition :
  precondition test2_nums test2_k := by
  simp [precondition, distinctElements, test2_nums, test2_k, List.eraseDups]
  native_decide

theorem test2_postcondition :
  postcondition test2_nums test2_k test2_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 ensures5 isSortedByFreqDesc countFreq
  unfold test2_nums test2_k test2_Expected
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ensures1: result.length = k
    native_decide
  · -- ensures2: ∀ x ∈ result, x ∈ nums
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · simp
    · simp
  · -- ensures3: result.Nodup
    native_decide
  · -- ensures4: isSortedByFreqDesc
    intro i j hij hjlen
    simp only [List.length_cons, List.length_nil] at hjlen
    -- j < 2, and i < j, so i can be 0 and j can be 1
    have hj : j = 1 := by omega
    have hi : i = 0 := by omega
    subst hi hj
    native_decide
  · -- ensures5: ∀ x ∈ nums, x ∉ result → ∀ y ∈ result, countFreq x nums ≤ countFreq y nums
    intro x hx hxnot y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx hy
    rcases hy with rfl | rfl
    · -- y = -1
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (first | native_decide | (simp at hxnot))
    · -- y = 2
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (first | native_decide | (simp at hxnot))

theorem test3_precondition :
  precondition test3_nums test3_k := by
  unfold precondition test3_nums test3_k distinctElements
  native_decide

theorem test3_postcondition :
  postcondition test3_nums test3_k test3_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 ensures4 ensures5
  unfold test3_nums test3_k test3_Expected
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ensures1: length = k
    native_decide
  · -- ensures2: all elements of result are in nums
    intro x hx
    simp only [List.mem_singleton] at hx
    simp [hx]
  · -- ensures3: nodup
    exact List.nodup_singleton 5
  · -- ensures4: sorted by frequency (vacuously true)
    unfold isSortedByFreqDesc
    intro i j hij hjlen
    simp only [List.length_singleton] at hjlen
    omega
  · -- ensures5: elements not in result have lower frequency
    intro x hx_nums hx_not_result
    simp only [List.mem_singleton] at hx_nums hx_not_result
    simp [hx_nums] at hx_not_result
end Proof
