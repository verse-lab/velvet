import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isStringSubseq (sub : String) (s : String) : Prop :=
  sub.toList.Sublist s.toList


def isCommonSubseq (sub : String) (s1 : String) (s2 : String) : Prop :=
  isStringSubseq sub s1 ∧ isStringSubseq sub s2



def ensures1 (s1 : String) (s2 : String) (result : String) :=
  isStringSubseq result s1


def ensures2 (s1 : String) (s2 : String) (result : String) :=
  isStringSubseq result s2


def ensures3 (s1 : String) (s2 : String) (result : String) :=
  ∀ other : String, isCommonSubseq other s1 s2 → other.length ≤ result.length

def precondition (s1 : String) (s2 : String) :=
  True

def postcondition (s1 : String) (s2 : String) (result : String) :=
  ensures1 s1 s2 result ∧
  ensures2 s1 s2 result ∧
  ensures3 s1 s2 result


def test1_s1 : String := "abcde"

def test1_s2 : String := "ace"

def test1_Expected : String := "ace"

def test3_s1 : String := "xyz"

def test3_s2 : String := "abc"

def test3_Expected : String := ""

def test4_s1 : String := "axbxc"

def test4_s2 : String := "abxc"

def test4_Expected : String := "abxc"







section Proof
theorem test1_precondition :
  precondition test1_s1 test1_s2 := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s1 test1_s2 test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 isStringSubseq isCommonSubseq
  unfold test1_s1 test1_s2 test1_Expected
  constructor
  · -- "ace" is sublist of "abcde"
    decide
  constructor
  · -- "ace" is sublist of "ace"
    decide
  · -- any common subsequence has length ≤ 3
    intro other h
    obtain ⟨_, h2⟩ := h
    -- other is a sublist of "ace" which has length 3
    have hlen : other.toList.length ≤ "ace".toList.length := List.Sublist.length_le h2
    -- "ace".toList.length = 3
    simp only [String.toList] at hlen
    -- Now we need other.length ≤ 3
    -- other.length is defined as other.toList.length (by String.length definition)
    show other.length ≤ 3
    unfold String.length
    simp only [String.toList, List.length] at hlen ⊢
    exact hlen

theorem test3_precondition :
  precondition test3_s1 test3_s2 := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition_0
    (h_unfold : postcondition test3_s1 test3_s2 test3_Expected ↔ ensures1 test3_s1 test3_s2 test3_Expected ∧ ensures2 test3_s1 test3_s2 test3_Expected ∧ ensures3 test3_s1 test3_s2 test3_Expected)
    (h_s1 : test3_s1 = "xyz")
    (h_s2 : test3_s2 = "abc")
    (h_exp : test3_Expected = "")
    : ensures1 test3_s1 test3_s2 test3_Expected := by
    unfold ensures1 isStringSubseq
    rw [h_s1, h_exp]
    native_decide

theorem test3_postcondition_1
    (h_unfold : postcondition test3_s1 test3_s2 test3_Expected ↔ ensures1 test3_s1 test3_s2 test3_Expected ∧ ensures2 test3_s1 test3_s2 test3_Expected ∧ ensures3 test3_s1 test3_s2 test3_Expected)
    (h_s1 : test3_s1 = "xyz")
    (h_s2 : test3_s2 = "abc")
    (h_exp : test3_Expected = "")
    (h_ensures1 : ensures1 test3_s1 test3_s2 test3_Expected)
    : ensures2 test3_s1 test3_s2 test3_Expected := by
    unfold ensures2 isStringSubseq
    rw [h_exp, h_s2]
    native_decide

theorem test3_postcondition_2
    (h_unfold : postcondition test3_s1 test3_s2 test3_Expected ↔ ensures1 test3_s1 test3_s2 test3_Expected ∧ ensures2 test3_s1 test3_s2 test3_Expected ∧ ensures3 test3_s1 test3_s2 test3_Expected)
    (h_s1 : test3_s1 = "xyz")
    (h_s2 : test3_s2 = "abc")
    (h_exp : test3_Expected = "")
    (h_ensures1 : ensures1 test3_s1 test3_s2 test3_Expected)
    (h_ensures2 : ensures2 test3_s1 test3_s2 test3_Expected)
    (h_xyz_chars : True)
    (h_abc_chars : True)
    : ensures3 test3_s1 test3_s2 test3_Expected := by
    unfold ensures3 isCommonSubseq isStringSubseq
    simp only [h_s1, h_s2, h_exp]
    intro other ⟨h_sub_xyz, h_sub_abc⟩
    -- other.toList is a sublist of both ['x', 'y', 'z'] and ['a', 'b', 'c']
    -- These have no common elements, so other.toList must be empty
    have h_subset_xyz : other.toList ⊆ ['x', 'y', 'z'] := List.Sublist.subset h_sub_xyz
    have h_subset_abc : other.toList ⊆ ['a', 'b', 'c'] := List.Sublist.subset h_sub_abc
    -- Show other.toList is empty by showing it's a subset of []
    have h_empty : other.toList = [] := by
      apply List.eq_nil_of_subset_nil
      intro c hc
      have hc_xyz := h_subset_xyz hc
      have hc_abc := h_subset_abc hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc_xyz hc_abc
      -- c is in {x, y, z} and {a, b, c}, but these are disjoint
      rcases hc_xyz with rfl | rfl | rfl <;> rcases hc_abc with h | h | h <;> simp_all
    -- Now other.length = 0 ≤ 0
    simp only [String.length]
    have h_data_empty : other.data = [] := h_empty
    simp [h_data_empty]

theorem test3_postcondition :
  postcondition test3_s1 test3_s2 test3_Expected := by
  -- First unfold all definitions to see what we need to prove
  have h_unfold : postcondition test3_s1 test3_s2 test3_Expected ↔ 
    ensures1 test3_s1 test3_s2 test3_Expected ∧ 
    ensures2 test3_s1 test3_s2 test3_Expected ∧ 
    ensures3 test3_s1 test3_s2 test3_Expected := by (try simp at *; expose_names); exact (Eq.to_iff rfl); done
  -- The concrete values
  have h_s1 : test3_s1 = "xyz" := by (try simp at *; expose_names); exact rfl; done
  have h_s2 : test3_s2 = "abc" := by (try simp at *; expose_names); exact rfl; done
  have h_exp : test3_Expected = "" := by (try simp at *; expose_names); exact rfl; done
  -- ensures1: "" is a subsequence of "xyz" (empty list is sublist of any list)
  have h_ensures1 : ensures1 test3_s1 test3_s2 test3_Expected := by (try simp at *; expose_names); exact (test3_postcondition_0 h_unfold h_s1 h_s2 h_exp); done
  -- ensures2: "" is a subsequence of "abc" (empty list is sublist of any list)
  have h_ensures2 : ensures2 test3_s1 test3_s2 test3_Expected := by (try simp at *; expose_names); exact (test3_postcondition_1 h_unfold h_s1 h_s2 h_exp h_ensures1); done
  -- For ensures3, we need to show any common subsequence has length ≤ 0
  -- Key: the character sets of "xyz" and "abc" are disjoint
  have h_xyz_chars : "xyz".toList = ['x', 'y', 'z'] := by (try simp at *; expose_names); exact (rfl); done
  have h_abc_chars : "abc".toList = ['a', 'b', 'c'] := by (try simp at *; expose_names); exact (rfl); done
  -- If other is a common subsequence, other.toList is a sublist of both
  -- By List.Sublist.subset, elements of other must be in both lists
  -- Since the lists are disjoint, other must be empty
  have h_ensures3 : ensures3 test3_s1 test3_s2 test3_Expected := by (try simp at *; expose_names); exact (test3_postcondition_2 h_unfold h_s1 h_s2 h_exp h_ensures1 h_ensures2 h_xyz_chars h_abc_chars); done
  -- Combine all three ensures to get the postcondition
  unfold postcondition
  exact ⟨h_ensures1, h_ensures2, h_ensures3⟩

theorem test4_precondition :
  precondition test4_s1 test4_s2 := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_s1 test4_s2 test4_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 isStringSubseq isCommonSubseq
  unfold test4_s1 test4_s2 test4_Expected
  constructor
  · -- ensures1: "abxc" is sublist of "axbxc"
    native_decide
  · constructor
    · -- ensures2: "abxc" is sublist of "abxc"
      native_decide
    · -- ensures3: any common subsequence has length ≤ 4
      intro other ⟨_, h2⟩
      have h_len : other.toList.length ≤ "abxc".toList.length := List.Sublist.length_le h2
      simp only [String.toList] at h_len
      unfold String.length
      simp only [String.toList]
      exact h_len
end Proof
