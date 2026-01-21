import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    rotateRight: Rotate a list of integers to the right by n positions.
    Natural language breakdown:
    1. Inputs are a list l : List Int and a rotation amount n : Nat.
    2. Rotating to the right by k means elements shift right; elements that pass the end reappear at the front.
    3. Rotation is cyclic and depends only on k modulo l.length.
    4. The output list must have the same length as l.
    5. If l is empty, rotating yields the empty list.
    6. For a nonempty list l with length m and r := n % m, the element at output index i equals
       the element at input index (i + (m - r)) % m.
-/

section Specs
-- Helper: index-based characterization of a right rotation.
-- We use Nat indexing with get! and explicit bounds.
-- For the empty list, the result must be empty.
def isRotateRight (l : List Int) (n : Nat) (result : List Int) : Prop :=
  result.length = l.length ∧
  (l = [] → result = []) ∧
  (l ≠ [] →
    let m := l.length
    let r := n % m
    ∀ i : Nat, i < m →
      result[i]! = l[(i + (m - r)) % m]!)

-- Preconditions
-- n : Nat is already non-negative.
def precondition (l : List Int) (n : Nat) : Prop :=
  True

-- Postconditions
-- The result is uniquely characterized by length + index mapping (for nonempty) and empty-list behavior.
def postcondition (l : List Int) (n : Nat) (result : List Int) : Prop :=
  isRotateRight l n result
end Specs

section Impl
method rotateRight (l : List Int) (n : Nat)
  return (result : List Int)
  require precondition l n
  ensures postcondition l n result
  do
  if l = [] then
    return []
  else
    let m := l.length
    let r := n % m
    let shift := m - r

    let mut acc : List Int := []
    let mut i : Nat := 0
    while i < m
      -- i is always within bounds; init i=0, preserved by i := i+1 under guard i<m.
      invariant "inv_i_bounds" i ≤ m
      -- `m` is the length of a nonempty list, hence positive; needed for `% m` bounds and safe indexing.
      invariant "inv_m_pos" 0 < m
      -- acc is exactly the list of the first i rotated elements, hence length = i.
      invariant "inv_acc_len" acc.length = i
      -- Strong spec aligned with postcondition: index mapping via get! for all built prefix elements.
      -- Init: vacuous at i=0. Preserved: appending v extends spec to i+1.
      invariant "inv_acc_spec_get" (∀ j : Nat, j < i → acc[j]! = l[(j + (m - r)) % m]! )
      done_with i = m
    do
      let idx := (i + shift) % m
      let v := l[idx]!
      acc := acc ++ [v]
      i := i + 1

    return acc
end Impl

section TestCases
-- Test case 1: example from prompt
-- rotateRight([1,2,3,4,5], 2) = [4,5,1,2,3]
def test1_l : List Int := [1, 2, 3, 4, 5]
def test1_n : Nat := 2
def test1_Expected : List Int := [4, 5, 1, 2, 3]

-- Test case 2: rotation larger than length (uses modulo)
def test2_l : List Int := [1, 2, 3, 4, 5]
def test2_n : Nat := 7
def test2_Expected : List Int := [4, 5, 1, 2, 3]

-- Test case 3: zero rotation
def test3_l : List Int := [1, 2, 3, 4, 5]
def test3_n : Nat := 0
def test3_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 4: empty list remains empty
def test4_l : List Int := []
def test4_n : Nat := 2
def test4_Expected : List Int := []

-- Test case 5: single-element list is unchanged for any n
def test5_l : List Int := [42]
def test5_n : Nat := 123
def test5_Expected : List Int := [42]

-- Test case 6: n is multiple of length
def test6_l : List Int := [10, -1, 7]
def test6_n : Nat := 3
def test6_Expected : List Int := [10, -1, 7]

-- Test case 7: rotate by 1
def test7_l : List Int := [10, -1, 7]
def test7_n : Nat := 1
def test7_Expected : List Int := [7, 10, -1]

-- Test case 8: list with duplicates
def test8_l : List Int := [2, 2, 3, 2]
def test8_n : Nat := 2
def test8_Expected : List Int := [3, 2, 2, 2]

-- Test case 9: two-element list, large n
def test9_l : List Int := [-5, 9]
def test9_n : Nat := 5
def test9_Expected : List Int := [9, -5]

-- Recommend to validate: test1, test2, test4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((rotateRight test1_l test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((rotateRight test2_l test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((rotateRight test3_l test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((rotateRight test4_l test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((rotateRight test5_l test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((rotateRight test6_l test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((rotateRight test7_l test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((rotateRight test8_l test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((rotateRight test9_l test9_n).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for rotateRight
prove_precondition_decidable_for rotateRight
prove_postcondition_decidable_for rotateRight
derive_tester_for rotateRight
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (List Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Nat)
    let res := rotateRightTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct rotateRight by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (l : List ℤ)
    (n : ℕ)
    (require_1 : precondition l n)
    (if_pos : l = [])
    : postcondition l n [] := by
  unfold postcondition
  unfold isRotateRight
  constructor
  · simp [if_pos]
  constructor
  · intro _
    rfl
  · intro hne
    exfalso
    exact hne if_pos

theorem goal_1
    (l : List ℤ)
    (n : ℕ)
    (require_1 : precondition l n)
    (if_neg : ¬l = [])
    : 0 < l.length := by
    intros; expose_names; exact (List.length_pos.mpr if_neg); done

theorem goal_2
    (l : List ℤ)
    (n : ℕ)
    (require_1 : precondition l n)
    (if_neg : ¬l = [])
    (acc : List ℤ)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ l.length)
    (invariant_inv_m_pos : 0 < l.length)
    (invariant_inv_acc_len : acc.length = i)
    (done_1 : i = l.length)
    (i_1 : List ℤ)
    (i_2 : ℕ)
    (invariant_inv_acc_spec_get : ∀ j < i, acc[j]?.getD 0 = l[(j + (l.length - n % l.length)) % l.length]?.getD 0)
    (i_3 : acc = i_1 ∧ i = i_2)
    : postcondition l n i_1 := by
  rcases i_3 with ⟨hacc, _hi⟩
  unfold postcondition
  unfold isRotateRight
  constructor
  · -- length
    have : acc.length = l.length := by
      calc
        acc.length = i := invariant_inv_acc_len
        _ = l.length := done_1
    simpa [hacc] using this
  constructor
  · -- empty-list behavior
    intro hl
    exact (if_neg hl).elim
  · -- main rotation index spec
    intro _hne
    dsimp
    intro k hk
    have hk' : k < i := by
      -- hk : k < m where m = l.length; use done_1 : i = l.length
      simpa [done_1] using hk
    have hspec :
        acc[k]?.getD 0 =
          l[(k + (l.length - n % l.length)) % l.length]?.getD 0 :=
      invariant_inv_acc_spec_get k hk'
    -- turn get! into getD/default form on the left
    -- and rewrite `acc` to `i_1`
    simpa [hacc, List.getD, List.get!_eq_getD] using hspec


prove_correct rotateRight by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 l n require_1 if_pos)
  exact (goal_1 l n require_1 if_neg)
  exact (goal_2 l n require_1 if_neg acc i invariant_inv_i_bounds invariant_inv_m_pos invariant_inv_acc_len done_1 i_1 i_2 invariant_inv_acc_spec_get i_3)
end Proof
