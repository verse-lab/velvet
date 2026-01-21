import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isStrictlyIncreasing (l : List Int) : Prop :=
  ∀ i : Nat, i + 1 < l.length → l[i]! < l[i + 1]!


def isSubseqOf (sub : List Int) (main : List Int) : Prop :=
  sub.Sublist main

def isIncreasingSubseqOf (sub : List Int) (main : List Int) : Prop :=
  isSubseqOf sub main ∧ isStrictlyIncreasing sub



def precondition (nums : List Int) : Prop :=
  True





def postcondition (nums : List Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ sub : List Int, isIncreasingSubseqOf sub nums ∧ sub.length = result.toNat) ∧
  (∀ sub : List Int, isIncreasingSubseqOf sub nums → sub.length ≤ result.toNat)


def test1_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]

def test1_Expected : Int := 4

def test3_nums : List Int := [7, 7, 7, 7, 7, 7, 7]

def test3_Expected : Int := 1

def test6_nums : List Int := []

def test6_Expected : Int := 0







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition_0
    (h_sublist : [2, 3, 7, 101].Sublist [10, 9, 2, 5, 3, 7, 101, 18])
    (h_unfold : postcondition test1_nums test1_Expected ↔ postcondition [10, 9, 2, 5, 3, 7, 101, 18] 4)
    (h_nonneg : True)
    (h_witness : True)
    : isStrictlyIncreasing [2, 3, 7, 101] := by
    unfold isStrictlyIncreasing
    intro i hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | n + 3 => simp only [List.length_cons, List.length_nil] at hi; omega

theorem test1_postcondition_1
    (h_sublist : [2, 3, 7, 101].Sublist [10, 9, 2, 5, 3, 7, 101, 18])
    (h_increasing : isStrictlyIncreasing [2, 3, 7, 101])
    (h_unfold : postcondition test1_nums test1_Expected ↔ postcondition [10, 9, 2, 5, 3, 7, 101, 18] 4)
    (h_nonneg : True)
    (h_witness : True)
    : isIncreasingSubseqOf [2, 3, 7, 101] [10, 9, 2, 5, 3, 7, 101, 18] := by
    unfold isIncreasingSubseqOf isSubseqOf
    constructor
    · -- Need to prove: [(2 : Int), 3, 7, 101].Sublist [10, 9, 2, 5, 3, 7, 101, 18]
      apply List.Sublist.cons
      apply List.Sublist.cons
      apply List.Sublist.cons₂
      apply List.Sublist.cons
      apply List.Sublist.cons₂
      apply List.Sublist.cons₂
      apply List.Sublist.cons₂
      apply List.Sublist.cons
      exact List.Sublist.slnil
    · exact h_increasing
end Proof
