import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def containsAllUpToK (collected : List Nat) (k : Nat) : Prop :=
  ∀ i : Nat, 1 ≤ i ∧ i ≤ k → i ∈ collected

def listSuffix (l : List Nat) (n : Nat) : List Nat :=
  l.drop (l.length - n)



def require1 (nums : List Nat) (k : Nat) :=
  containsAllUpToK nums k

def precondition (nums : List Nat) (k : Nat) :=
  require1 nums k



def ensures1 (nums : List Nat) (k : Nat) (result : Nat) :=
  result ≤ nums.length


def ensures2 (nums : List Nat) (k : Nat) (result : Nat) :=
  containsAllUpToK (listSuffix nums result) k


def ensures3 (nums : List Nat) (k : Nat) (result : Nat) :=
  ∀ m : Nat, m < result → ¬containsAllUpToK (listSuffix nums m) k

def postcondition (nums : List Nat) (k : Nat) (result : Nat) :=
  ensures1 nums k result ∧
  ensures2 nums k result ∧
  ensures3 nums k result


def test1_nums : List Nat := [3, 1, 5, 4, 2]

def test1_k : Nat := 2

def test1_Expected : Nat := 4

def test4_nums : List Nat := [5, 4, 3, 2, 1]

def test4_k : Nat := 1

def test4_Expected : Nat := 1

def test8_nums : List Nat := [1, 2, 3]

def test8_k : Nat := 0

def test8_Expected : Nat := 0







section Proof
theorem test1_precondition :
  precondition test1_nums test1_k := by
  unfold precondition require1 containsAllUpToK test1_nums test1_k
  intro i ⟨h1, h2⟩
  -- i is between 1 and 2, so i = 1 or i = 2
  have : i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl
  · decide
  · decide

theorem test1_postcondition :
  postcondition test1_nums test1_k test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 containsAllUpToK listSuffix
  unfold test1_nums test1_k test1_Expected
  simp only [List.length_cons, List.length_nil]
  constructor
  · -- ensures1: 4 ≤ 5
    omega
  constructor
  · -- ensures2: all i with 1 ≤ i ≤ 2 are in the suffix [1, 5, 4, 2]
    intro i ⟨hi_lower, hi_upper⟩
    simp only [List.drop_succ_cons, List.drop_zero]
    -- i is 1 or 2 based on the bounds
    have hi_bounds : i = 1 ∨ i = 2 := by omega
    cases hi_bounds with
    | inl h => simp [h]
    | inr h => simp [h]
  · -- ensures3: for all m < 4, not all of 1..2 are in suffix of length m
    intro m hm
    intro h
    -- For m < 4, the suffix doesn't contain 1 (except when m >= 4)
    -- listSuffix [3, 1, 5, 4, 2] m = drop (5 - m) [3, 1, 5, 4, 2]
    have h1 := h 1 (And.intro (Nat.le_refl 1) (by omega : 1 ≤ 2))
    -- Need to show 1 is not in the suffix for m < 4
    interval_cases m
    · -- m = 0: drop 5 gives []
      simp at h1
    · -- m = 1: drop 4 gives [2]
      simp at h1
    · -- m = 2: drop 3 gives [4, 2]
      simp at h1
    · -- m = 3: drop 2 gives [5, 4, 2]
      simp at h1

theorem test4_precondition :
  precondition test4_nums test4_k := by
  unfold precondition require1 containsAllUpToK test4_nums test4_k
  intro i ⟨h1, h2⟩
  have : i = 1 := Nat.le_antisymm h2 h1
  subst this
  decide

theorem test4_postcondition :
  postcondition test4_nums test4_k test4_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 containsAllUpToK listSuffix
  unfold test4_nums test4_k test4_Expected
  simp only [List.length_cons, List.length_nil]
  constructor
  · -- ensures1: 1 ≤ 5
    omega
  constructor
  · -- ensures2: all i with 1 ≤ i ≤ 1 are in [1]
    intro i ⟨hi_lo, hi_hi⟩
    have h : i = 1 := by omega
    subst h
    native_decide
  · -- ensures3: for all m < 1, suffix of length m doesn't contain all 1..1
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    simp only [Nat.sub_zero, List.drop_length]
    intro h
    have := h 1 ⟨le_refl 1, le_refl 1⟩
    exact List.not_mem_nil this

theorem test8_precondition :
  precondition test8_nums test8_k := by
  unfold precondition require1 containsAllUpToK test8_nums test8_k
  intro i ⟨h1, h2⟩
  omega

theorem test8_postcondition :
  postcondition test8_nums test8_k test8_Expected := by
  unfold postcondition ensures1 ensures2 ensures3
  unfold test8_nums test8_k test8_Expected
  constructor
  · -- ensures1: 0 ≤ 3
    omega
  constructor
  · -- ensures2: containsAllUpToK (listSuffix [1, 2, 3] 0) 0
    unfold containsAllUpToK
    intro i ⟨h1, h2⟩
    -- h1: 1 ≤ i, h2: i ≤ 0, which is impossible
    omega
  · -- ensures3: ∀ m < 0, ¬containsAllUpToK (listSuffix [1, 2, 3] m) 0
    intro m hm
    -- hm: m < 0, which is impossible for natural numbers
    omega

theorem uniqueness (nums : List Nat) (k : Nat):
  precondition nums k →
  (∀ ret1 ret2,
    postcondition nums k ret1 →
    postcondition nums k ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- Extract components from postconditions
  obtain ⟨_hens1_1, hens2_1, hens3_1⟩ := hpost1
  obtain ⟨_hens1_2, hens2_2, hens3_2⟩ := hpost2
  -- Use antisymmetry: prove ret1 ≤ ret2 and ret2 ≤ ret1
  apply Nat.le_antisymm
  -- Prove ret1 ≤ ret2
  · by_contra h
    push_neg at h
    -- h : ret2 < ret1
    -- By ensures3 of ret1 with m = ret2, since ret2 < ret1:
    -- suffix of length ret2 does NOT contain all 1..k
    have hnotcontains := hens3_1 ret2 h
    -- But ensures2 of ret2 says suffix of length ret2 DOES contain all 1..k
    exact hnotcontains hens2_2
  -- Prove ret2 ≤ ret1
  · by_contra h
    push_neg at h
    -- h : ret1 < ret2
    -- By ensures3 of ret2 with m = ret1, since ret1 < ret2:
    -- suffix of length ret1 does NOT contain all 1..k
    have hnotcontains := hens3_2 ret1 h
    -- But ensures2 of ret1 says suffix of length ret1 DOES contain all 1..k
    exact hnotcontains hens2_1
end Proof
