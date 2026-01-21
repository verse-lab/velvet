import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isSortedAsc (xs : List Int) : Prop :=
  List.Sorted (· ≤ ·) xs


def isPermOf (xs : List Int) (ys : List Int) : Prop :=
  List.Perm xs ys



def precondition (xs : List Int) : Prop :=
  True



def postcondition (xs : List Int) (result : List Int) : Prop :=
  isSortedAsc result ∧ isPermOf result xs


def test1_xs : List Int := [3, 1, 4, 2]

def test1_Expected : List Int := [1, 2, 3, 4]

def test2_xs : List Int := []

def test2_Expected : List Int := []

def test4_xs : List Int := [5, -1, 0, 10, -1]

def test4_Expected : List Int := [-1, -1, 0, 5, 10]







section Proof
theorem test1_precondition :
  precondition test1_xs := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_xs test1_Expected := by
  unfold postcondition isSortedAsc isPermOf test1_xs test1_Expected
  constructor
  · native_decide
  · native_decide

theorem test2_precondition :
  precondition test2_xs := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_xs test2_Expected := by
  unfold postcondition isSortedAsc isPermOf test2_xs test2_Expected
  constructor
  · exact List.sorted_nil
  · exact List.Perm.nil

theorem test4_precondition :
  precondition test4_xs := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_xs test4_Expected := by
  unfold postcondition isSortedAsc isPermOf test4_xs test4_Expected
  constructor
  · native_decide
  · native_decide

theorem uniqueness (xs : List Int):
  precondition xs →
  (∀ ret1 ret2,
    postcondition xs ret1 →
    postcondition xs ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  -- Extract the components from postconditions
  obtain ⟨hsorted1, hperm1⟩ := hpost1
  obtain ⟨hsorted2, hperm2⟩ := hpost2
  -- ret1 is a permutation of xs, and ret2 is a permutation of xs
  -- So ret1 is a permutation of ret2
  have hperm : List.Perm ret1 ret2 := List.Perm.trans hperm1 hperm2.symm
  -- Both are sorted (Sorted is Pairwise)
  unfold isSortedAsc at hsorted1 hsorted2
  unfold List.Sorted at hsorted1 hsorted2
  -- Apply the key lemma: sorted permutations are equal for antisymmetric relations
  apply List.Perm.eq_of_sorted _ hsorted1 hsorted2 hperm
  -- Now prove the antisymmetry condition
  intro a b _ _ hab hba
  exact Int.le_antisymm hab hba
end Proof
