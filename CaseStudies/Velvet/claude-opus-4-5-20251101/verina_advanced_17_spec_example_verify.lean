import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (l : List Int) : Prop :=
  True





def postcondition (l : List Int) (result : List Int) : Prop :=
  List.Sorted (· ≤ ·) result ∧ List.Perm l result


def test1_l : List Int := []

def test1_Expected : List Int := []

def test4_l : List Int := [3, 2, 1]

def test4_Expected : List Int := [1, 2, 3]

def test5_l : List Int := [4, 2, 2, 3]

def test5_Expected : List Int := [2, 2, 3, 4]







section Proof
theorem test1_precondition :
  precondition test1_l := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_l test1_Expected := by
  unfold postcondition test1_l test1_Expected
  constructor
  · exact List.sorted_nil
  · exact List.Perm.refl []

theorem test4_precondition :
  precondition test4_l := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_l test4_Expected := by
  unfold postcondition test4_l test4_Expected
  constructor
  · -- Sorted [1, 2, 3]
    native_decide
  · -- Perm [3, 2, 1] [1, 2, 3]
    native_decide

theorem test5_precondition :
  precondition test5_l := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition :
  postcondition test5_l test5_Expected := by
  unfold postcondition test5_l test5_Expected
  constructor
  · native_decide
  · native_decide

theorem uniqueness (l : List Int):
  precondition l →
  (∀ ret1 ret2,
    postcondition l ret1 →
    postcondition l ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  obtain ⟨hsorted1, hperm1⟩ := hpost1
  obtain ⟨hsorted2, hperm2⟩ := hpost2
  -- Get permutation between ret1 and ret2
  have hperm : List.Perm ret1 ret2 := List.Perm.trans (List.Perm.symm hperm1) hperm2
  -- Apply the uniqueness lemma for sorted lists
  apply List.Perm.eq_of_sorted _ hsorted1 hsorted2 hperm
  -- Prove antisymmetry for Int's ≤
  intro a b _ _ hab hba
  exact Int.le_antisymm hab hba
end Proof
