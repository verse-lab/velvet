import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isStrictlyIncreasing (l : List Int) : Prop :=
  l.IsChain (· < ·)

def isIncreasingSubseq (sub : List Int) (xs : List Int) : Prop :=
  List.Sublist sub xs ∧ isStrictlyIncreasing sub



def precondition (xs : List Int) : Prop :=
  True






def postcondition (xs : List Int) (result : Nat) : Prop :=

  (∃ sub : List Int, isIncreasingSubseq sub xs ∧ sub.length = result) ∧

  (∀ sub : List Int, isIncreasingSubseq sub xs → sub.length ≤ result)


def test1_xs : List Int := [1, 2, 3, 4]

def test1_Expected : Nat := 4

def test3_xs : List Int := [1, 3, 2, 4, 0, 5]

def test3_Expected : Nat := 4

def test9_xs : List Int := [3, 3, 3, 3]

def test9_Expected : Nat := 1







section Proof
theorem test1_precondition :
  precondition test1_xs := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_xs test1_Expected := by
  unfold postcondition test1_xs test1_Expected
  constructor
  · -- Existence: [1, 2, 3, 4] is a strictly increasing subsequence of length 4
    use [1, 2, 3, 4]
    constructor
    · -- isIncreasingSubseq [1, 2, 3, 4] [1, 2, 3, 4]
      unfold isIncreasingSubseq
      constructor
      · -- [1, 2, 3, 4] is a sublist of [1, 2, 3, 4]
        exact List.Sublist.refl _
      · -- isStrictlyIncreasing [1, 2, 3, 4]
        unfold isStrictlyIncreasing
        decide
    · -- length is 4
      rfl
  · -- All strictly increasing subsequences have length ≤ 4
    intro sub h
    unfold isIncreasingSubseq at h
    obtain ⟨hsub, _⟩ := h
    have hlen : sub.length ≤ [1, 2, 3, 4].length := List.Sublist.length_le hsub
    simp at hlen
    exact hlen

theorem test3_precondition :
  precondition test3_xs := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition_0 : List.IsChain (fun x1 x2 ↦ x1 < x2) [1, 2, 4, 5] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test3_postcondition_1
    (sub : List ℤ)
    (hsub : sub.Sublist [1, 3, 2, 4, 0, 5])
    (hincr : isStrictlyIncreasing sub)
    (h_list_len : True)
    : sub.length ≤ 6 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )
end Proof
