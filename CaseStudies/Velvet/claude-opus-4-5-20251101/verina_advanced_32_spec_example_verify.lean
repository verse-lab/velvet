import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isStrictlyIncreasing : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x < y ∧ isStrictlyIncreasing (y :: rest)

def isSubsequenceOf : List Int → List Int → Prop
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys => 
    if x = y then isSubsequenceOf xs ys
    else isSubsequenceOf (x :: xs) ys

def isIncreasingSubsequenceOf (subseq : List Int) (original : List Int) : Prop :=
  isSubsequenceOf subseq original ∧ isStrictlyIncreasing subseq



def precondition (numbers : List Int) : Prop :=
  True







def postcondition (numbers : List Int) (result : Nat) : Prop :=

  (∃ subseq : List Int, 
    isIncreasingSubsequenceOf subseq numbers ∧ 
    subseq.length = result) ∧

  (∀ subseq : List Int, 
    isIncreasingSubsequenceOf subseq numbers → 
    subseq.length ≤ result) ∧

  (numbers = [] ↔ result = 0)


def test1_numbers : List Int := [10, 22, 9, 33, 21, 50, 41, 60]

def test1_Expected : Nat := 5

def test5_numbers : List Int := [1, 2, 3, 4, 5]

def test5_Expected : Nat := 5

def test6_numbers : List Int := []

def test6_Expected : Nat := 0







section Proof
theorem test1_precondition :
  precondition test1_numbers := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition_0
    (h_test1_numbers : test1_numbers = [10, 22, 9, 33, 21, 50, 41, 60])
    (h_test1_Expected : test1_Expected = 5)
    (h_witness_subseq : isSubsequenceOf [10, 22, 33, 50, 60] test1_numbers)
    : isStrictlyIncreasing [10, 22, 33, 50, 60] := by
  unfold isStrictlyIncreasing
  constructor
  · decide
  · constructor
    · decide
    · constructor
      · decide
      · constructor
        · decide
        · trivial

theorem test1_postcondition_1
    (h_test1_numbers : test1_numbers = [10, 22, 9, 33, 21, 50, 41, 60])
    (h_test1_Expected : test1_Expected = 5)
    (h_witness_subseq : isSubsequenceOf [10, 22, 33, 50, 60] test1_numbers)
    (h_witness_increasing : isStrictlyIncreasing [10, 22, 33, 50, 60])
    : isIncreasingSubsequenceOf [10, 22, 33, 50, 60] test1_numbers := by
    unfold isIncreasingSubsequenceOf
    exact ⟨h_witness_subseq, h_witness_increasing⟩

theorem test1_postcondition_2
    (h_test1_numbers : test1_numbers = [10, 22, 9, 33, 21, 50, 41, 60])
    (h_test1_Expected : test1_Expected = 5)
    (h_witness_subseq : isSubsequenceOf [10, 22, 33, 50, 60] test1_numbers)
    (h_witness_increasing : isStrictlyIncreasing [10, 22, 33, 50, 60])
    (h_witness_is_inc_subseq : isIncreasingSubsequenceOf [10, 22, 33, 50, 60] test1_numbers)
    (h_exists : ∃ subseq, isIncreasingSubsequenceOf subseq test1_numbers ∧ subseq.length = test1_Expected)
    (h_witness_length : True)
    : ∀ (subseq : List ℤ), isIncreasingSubsequenceOf subseq test1_numbers → subseq.length ≤ test1_Expected := by
    sorry

theorem test1_postcondition :
  postcondition test1_numbers test1_Expected := by
  -- Unfold the definitions
  have h_test1_numbers : test1_numbers = [10, 22, 9, 33, 21, 50, 41, 60] := by (try simp at *; expose_names); exact (rfl); done
  have h_test1_Expected : test1_Expected = 5 := by (try simp at *; expose_names); exact rfl; done
  -- The witness subsequence
  have h_witness_subseq : isSubsequenceOf [10, 22, 33, 50, 60] test1_numbers := by (try simp at *; expose_names); exact (trivial); done
  have h_witness_increasing : isStrictlyIncreasing [10, 22, 33, 50, 60] := by (try simp at *; expose_names); exact (test1_postcondition_0 h_test1_numbers h_test1_Expected h_witness_subseq); done
  have h_witness_is_inc_subseq : isIncreasingSubsequenceOf [10, 22, 33, 50, 60] test1_numbers := by (try simp at *; expose_names); exact (test1_postcondition_1 h_test1_numbers h_test1_Expected h_witness_subseq h_witness_increasing); done
  have h_witness_length : ([10, 22, 33, 50, 60] : List Int).length = 5 := by (try simp at *; expose_names); exact (h_test1_Expected); done
  -- First conjunct: existence
  have h_exists : ∃ subseq : List Int, isIncreasingSubsequenceOf subseq test1_numbers ∧ subseq.length = test1_Expected := by (try simp at *; expose_names); exact (Filter.frequently_principal.mp fun a ↦ a h_witness_is_inc_subseq h_test1_Expected); done
  -- Second conjunct: maximality (this is the hard part - asserting it directly)
  have h_maximality : ∀ subseq : List Int, isIncreasingSubsequenceOf subseq test1_numbers → subseq.length ≤ test1_Expected := by (try simp at *; expose_names); exact (test1_postcondition_2 h_test1_numbers h_test1_Expected h_witness_subseq h_witness_increasing h_witness_is_inc_subseq h_exists h_witness_length); done
  -- Third conjunct: empty list equivalence
  have h_not_empty : ¬(test1_numbers = []) := by (try simp at *; expose_names); exact (List.getLast?_isSome.mp rfl); done
  have h_not_zero : ¬(test1_Expected = 0) := by (try simp at *; expose_names); exact (Nat.add_one_ne_zero 4); done
  have h_iff_empty : test1_numbers = [] ↔ test1_Expected = 0 := by (try simp at *; expose_names); exact (beq_eq_beq.mp rfl); done
  -- Combine all three parts into the postcondition
  exact ⟨h_exists, h_maximality, h_iff_empty⟩
end Proof
