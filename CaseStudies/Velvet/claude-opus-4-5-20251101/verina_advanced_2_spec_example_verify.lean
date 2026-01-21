import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isCommonSubseq (s : List Int) (a : List Int) (b : List Int) : Prop :=
  List.Sublist s a ∧ List.Sublist s b



def ensures1 (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  ∃ s : List Int, isCommonSubseq s a.toList b.toList ∧ s.length = result.toNat


def ensures2 (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  ∀ s : List Int, isCommonSubseq s a.toList b.toList → s.length ≤ result.toNat


def ensures3 (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  result.toNat ≤ min a.size b.size

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  ensures1 a b result ∧
  ensures2 a b result ∧
  ensures3 a b result


def test1_a : Array Int := #[1, 2, 3]

def test1_b : Array Int := #[1, 2, 3]

def test1_Expected : Int := 3

def test2_a : Array Int := #[1, 3, 5, 7]

def test2_b : Array Int := #[1, 2, 3, 4, 5, 6, 7]

def test2_Expected : Int := 4

def test3_a : Array Int := #[1, 2, 3]

def test3_b : Array Int := #[4, 5, 6]

def test3_Expected : Int := 0







section Proof
theorem test1_precondition :
  precondition test1_a test1_b := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_b test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 isCommonSubseq
  unfold test1_a test1_b test1_Expected
  constructor
  · -- ensures1: exists a common subsequence of length 3
    use [1, 2, 3]
    constructor
    · constructor
      · exact List.Sublist.refl [1, 2, 3]
      · exact List.Sublist.refl [1, 2, 3]
    · native_decide
  constructor
  · -- ensures2: all common subsequences have length ≤ 3
    intro s ⟨hs_a, _⟩
    have h := List.Sublist.length_le hs_a
    simp only [Array.toList, List.length_cons, List.length_nil] at h
    omega
  · -- ensures3: 3 ≤ min 3 3
    native_decide

theorem test2_precondition :
  precondition test2_a test2_b := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_a test2_b test2_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 isCommonSubseq
  unfold test2_a test2_b test2_Expected
  constructor
  · -- ensures1: exists a common subsequence of length 4
    use [1, 3, 5, 7]
    constructor
    · constructor
      · -- [1, 3, 5, 7] is a sublist of [1, 3, 5, 7]
        exact List.Sublist.refl _
      · -- [1, 3, 5, 7] is a sublist of [1, 2, 3, 4, 5, 6, 7]
        native_decide
    · -- length [1, 3, 5, 7] = 4
      native_decide
  constructor
  · -- ensures2: all common subsequences have length ≤ 4
    intro s ⟨h1, h2⟩
    have : s.length ≤ [1, 3, 5, 7].length := List.Sublist.length_le h1
    simp at this
    exact this
  · -- ensures3: 4 ≤ min 4 7
    native_decide

theorem test3_precondition :
  precondition test3_a test3_b := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_a test3_b test3_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test3_a test3_b test3_Expected
  constructor
  · -- ensures1: exists common subsequence of length 0
    use []
    constructor
    · unfold isCommonSubseq
      constructor
      · exact List.nil_sublist _
      · exact List.nil_sublist _
    · rfl
  constructor
  · -- ensures2: all common subsequences have length ≤ 0
    intro s hs
    unfold isCommonSubseq at hs
    obtain ⟨hsA, hsB⟩ := hs
    -- s is a sublist of [1, 2, 3] and [4, 5, 6]
    -- These have disjoint elements, so s must be empty
    have h : s = [] := by
      by_contra hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil s hne
      have hxA : x ∈ [1, 2, 3] := hsA.subset hx
      have hxB : x ∈ [4, 5, 6] := hsB.subset hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hxA hxB
      rcases hxA with rfl | rfl | rfl
      · -- x = 1
        rcases hxB with h1 | h2 | h3 <;> omega
      · -- x = 2
        rcases hxB with h1 | h2 | h3 <;> omega
      · -- x = 3
        rcases hxB with h1 | h2 | h3 <;> omega
    simp [h]
  · -- ensures3: 0 ≤ min 3 3
    simp
end Proof
